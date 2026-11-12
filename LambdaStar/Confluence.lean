import LambdaStar.Reduction

namespace LambdaStar

/-- Two terms are joinable at stage `n` when `a ↦ₙ* c ↤ₙ* b`. -/
def JoinableAt (Δ : DefEnv) (stage : Nat) (left right : Term) : Prop :=
  ∃ join, Steps Δ stage left join ∧ Steps Δ stage right join

/-- Confluence of the reduction relation at one certification stage. -/
def ConfluentAt (Δ : DefEnv) (stage : Nat) : Prop :=
  ∀ {source left right},
    Steps Δ stage source left →
    Steps Δ stage source right →
    JoinableAt Δ stage left right

/-- Every finite certification stage is confluent. -/
def StagedConfluent (Δ : DefEnv) : Prop :=
  ∀ stage, ConfluentAt Δ stage

/-- Idempotence witnessed at one particular certification stage. -/
def IdempotentAt (Δ : DefEnv) (stage : Nat) (u : Term) : Prop :=
  Steps Δ stage (idempotenceLhs u) (idempotenceRhs u)

/-- The pointwise instance `u (u t) ↦ₙ* u t` of idempotence. -/
def IdempotentOn (Δ : DefEnv) (stage : Nat) (u term : Term) : Prop :=
  Steps Δ stage (.app u (.app u term)) (.app u term)

/-- Instantiating `λx. u (u x) ↦ₙ* λx. u x` yields `u (u t) ↦ₙ* u t`. -/
theorem IdempotentAt.on (certificate : IdempotentAt Δ stage u) (term : Term) :
  IdempotentOn Δ stage u term := by
  have bodyReduction := Steps.invert_lam certificate
  have instantiated := Steps.substAt bodyReduction 0 term
  simpa [IdempotentOn, idempotenceLhs, idempotenceRhs, Term.substAt,
    Term.substAt_shift_succ, Term.shift_zero] using instantiated

/-- Joinability for the stage-erased reduction `↦*`. -/
def Joinable (Δ : DefEnv) (left right : Term) : Prop :=
  ∃ join, Reduces Δ left join ∧ Reduces Δ right join

/--
Finite derivations at stages `m` and `n` can both be promoted to `m + n`.
This is the point at which stage monotonicity enters the confluence proof.
-/
theorem Steps.alignStages
    (left : Steps Δ leftStage source leftResult)
    (right : Steps Δ rightStage source rightResult) :
    Steps Δ (leftStage + rightStage) source leftResult ∧
      Steps Δ (leftStage + rightStage) source rightResult := by
  constructor
  · exact left.monoAdd rightStage
  · simpa [Nat.add_comm] using right.monoAdd leftStage

/--
The principal star/star critical peak is joinable once the idempotence
certificate has been instantiated at `term`:

                    * u (* u t)
                    /          \
                   /            \
              * u t            u (u t)
                   \            /
                    \          /
                         u t

The pointwise instance is supplied by `IdempotentAt.on`, proved by stability
of reduction under capture-avoiding substitution.
-/
theorem starredIdempotence_starChecking_join
    (certificate : IdempotentAt Δ stage u)
    (instanceAtTerm : IdempotentOn Δ stage u term) :
    JoinableAt Δ (stage + 1)
      (.app (.app .star u) term)
      (.app u (.app u term)) := by
  refine ⟨.app u term, ?_, ?_⟩
  · exact Steps.single (.appLeft (.starChecking certificate))
  · exact instanceAtTerm.monoSucc

/-- Both arms of the principal critical peak are genuine reductions. -/
theorem starredIdempotence_starChecking_peak
    (certificate : IdempotentAt Δ stage u)
    (instanceAtTerm : IdempotentOn Δ stage u term) :
    let source := .app (.app .star u) (.app (.app .star u) term)
    let collapsed := .app (.app .star u) term
    let checked := .app u (.app u term)
    Steps Δ (stage + 1) source collapsed ∧
      Steps Δ (stage + 1) source checked ∧
      JoinableAt Δ (stage + 1) collapsed checked := by
  dsimp
  refine ⟨Steps.single .starredIdempotence, ?_,
    starredIdempotence_starChecking_join certificate instanceAtTerm⟩
  exact .tail (.appLeft (.starChecking certificate))
    (Steps.single (.appRight (.appLeft (.starChecking certificate))))

/-- Stage-wise confluence implies confluence after hiding the finite stage. -/
theorem Reduces.confluent (confluent : StagedConfluent Δ)
  (left : Reduces Δ source leftResult)
  (right : Reduces Δ source rightResult) :
  Joinable Δ leftResult rightResult := by
  obtain ⟨leftStage, left⟩ := left
  obtain ⟨rightStage, right⟩ := right
  obtain ⟨left, right⟩ := Steps.alignStages left right
  obtain ⟨join, leftToJoin, rightToJoin⟩ :=
    confluent (leftStage + rightStage) left right
  exact ⟨join,
    ⟨leftStage + rightStage, leftToJoin⟩,
    ⟨leftStage + rightStage, rightToJoin⟩⟩

/-- A normal form has no outgoing reduction at any finite stage. -/
def NormalForm (Δ : DefEnv) (term : Term) : Prop :=
  ∀ {result}, ReducesOne Δ term result → False

/-- A normal form cannot reduce non-trivially by zero or more steps. -/
theorem NormalForm.eq_of_steps (normal : NormalForm Δ term)
  (reduction : Steps Δ stage term result) : result = term := by
  cases reduction with
  | refl => rfl
  | tail head _ => exact False.elim (normal ⟨stage, head⟩)

/-- Confluence gives the desired uniqueness of normal forms. -/
theorem normalForm_unique (confluent : StagedConfluent Δ)
  (leftNormal : NormalForm Δ left)
  (rightNormal : NormalForm Δ right)
  (toLeft : Reduces Δ source left)
  (toRight : Reduces Δ source right) : left = right := by
  obtain ⟨join, ⟨leftStage, leftToJoin⟩, ⟨rightStage, rightToJoin⟩⟩ :=
    Reduces.confluent confluent toLeft toRight
  calc
    left = join := (leftNormal.eq_of_steps leftToJoin).symm
    _ = right := rightNormal.eq_of_steps rightToJoin

end LambdaStar
