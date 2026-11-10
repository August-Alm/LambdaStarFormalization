import LambdaStar.Syntax

namespace LambdaStar

open Term

/-- `λx. u (u x)`, with the free variables of `u` shifted under `λ`. -/
def idempotenceLhs (u : Term) : Term :=
  .lam (.app (u.shift 1 0) (.app (u.shift 1 0) (.bvar 0)))

/-- `λx. u x`, with the free variables of `u` shifted under `λ`. -/
def idempotenceRhs (u : Term) : Term :=
  .lam (.app (u.shift 1 0) (.bvar 0))

/-
Reduction is stratified to make the star-checking premise well-founded.
Stage `0` contains β, deterministic unfolding, and starred idempotence.
Stage `n + 1` may additionally use an idempotence derivation from stage `n`.
-/
mutual
  inductive Step (Δ : DefEnv) : Nat → Term → Term → Prop where
    /-- `(λx. t) u ↦ t{x := u}`. -/
    | beta : Step Δ stage (.app (.lam body) argument)
        (body.instantiate argument)
    /-- `μX.F(X) ↦ F(μX.F(X))`. -/
    | muUnfold : Step Δ stage (.mu body) body.unfoldMu
    /-- `c ↦ Δ(c)`. The functional environment makes unfolding deterministic. -/
    | delta (defined : Δ.defs name = some body) :
        Step Δ stage (.const name) body
    /-- `* u (* u t) ↦ * u t`. -/
    | starredIdempotence :
        Step Δ stage
          (.app (.app .star u) (.app (.app .star u) term))
          (.app (.app .star u) term)
    /--
    The certified star-checking rule:

        Δ ⊢ Idempotent u
        ─────────────────
             * u ↦ u

    At stage `n + 1`, the certificate is a finite reduction at stage `n`.
    -/
    | starChecking
        (certificate : Steps Δ stage (idempotenceLhs u) (idempotenceRhs u)) :
        Step Δ (stage + 1) (.app .star u) u
    | lam : Step Δ stage body body' →
        Step Δ stage (.lam body) (.lam body')
    | mu : Step Δ stage body body' →
      Step Δ stage (.mu body) (.mu body')
    | appLeft : Step Δ stage function function' →
        Step Δ stage (.app function argument) (.app function' argument)
    | appRight : Step Δ stage argument argument' →
        Step Δ stage (.app function argument) (.app function argument')

  /-- Reflexive-transitive closure of reduction at a fixed stage. -/
  inductive Steps (Δ : DefEnv) : Nat → Term → Term → Prop where
    | refl : Steps Δ stage term term
    | tail : Step Δ stage term middle → Steps Δ stage middle result →
        Steps Δ stage term result
end

namespace Steps

theorem single (step : Step Δ stage term result) : Steps Δ stage term result :=
  .tail step .refl

end Steps

/-- Substitution transforms `λx. u (u x)` pointwise in `u`. -/
theorem substAt_idempotenceLhs (u replacement : Term) (depth : Nat) :
    Term.substAt depth replacement (idempotenceLhs u) =
      idempotenceLhs (Term.substAt depth replacement u) := by
  simp [idempotenceLhs, Term.substAt, Term.substAt_shift_one]

/-- Substitution transforms `λx. u x` pointwise in `u`. -/
theorem substAt_idempotenceRhs (u replacement : Term) (depth : Nat) :
    Term.substAt depth replacement (idempotenceRhs u) =
      idempotenceRhs (Term.substAt depth replacement u) := by
  simp [idempotenceRhs, Term.substAt, Term.substAt_shift_one]

/-- A step out of a lambda is necessarily a step in its body. -/
theorem Step.invert_lam (reduction : Step Δ stage (.lam body) result) :
    ∃ body', result = .lam body' ∧ Step Δ stage body body' := by
  cases reduction with
  | lam reduction => exact ⟨_, rfl, reduction⟩

/-
Reduction is stable under capture-avoiding substitution. The proof is mutual
because a star-checking step recursively transforms its `↦*` certificate.
-/
mutual
  theorem Step.substAt {stage term result}
      (reduction : Step Δ stage term result) (depth : Nat) (replacement : Term) :
      Step Δ stage (Term.substAt depth replacement term)
        (Term.substAt depth replacement result) :=
    match reduction with
    | @Step.beta _ _ body argument => by
        simpa [Term.substAt, Term.substAt_instantiate] using
          (Step.beta (Δ := Δ)
            (body := Term.substAt (depth + 1) replacement body)
            (argument := Term.substAt depth replacement argument))
    | @Step.muUnfold _ _ body => by
        simpa [Term.substAt, Term.substAt_unfoldMu] using
          (Step.muUnfold (Δ := Δ)
            (body := Term.substAt (depth + 1) replacement body))
    | @Step.delta _ _ body _ defined => by
        have hClosed := Δ.closed _ _ defined
        have hBody : Term.substAt depth replacement body = body :=
          Term.substAt_eq_self_of_wellScoped
            (replacement := replacement) (hClosed.mono (Nat.zero_le depth))
        simpa [Term.substAt, hBody] using
          (Step.delta (Δ := Δ) defined)
    | @Step.starredIdempotence _ _ u term => by
        simpa [Term.substAt] using
          (Step.starredIdempotence (Δ := Δ)
            (u := Term.substAt depth replacement u)
            (term := Term.substAt depth replacement term))
    | @Step.starChecking _ stage u certificate => by
        have transformed := Steps.substAt certificate depth replacement
        have transformedCertificate := by
          simpa [substAt_idempotenceLhs, substAt_idempotenceRhs] using transformed
        simpa [Term.substAt] using
          (Step.starChecking transformedCertificate)
    | @Step.lam _ _ body body' reduction => by
        simpa [Term.substAt] using
          (Step.lam (Step.substAt reduction (depth + 1) replacement))
    | @Step.mu _ _ body body' reduction => by
        simpa [Term.substAt] using
          (Step.mu (Step.substAt reduction (depth + 1) replacement))
    | @Step.appLeft _ _ function function' argument reduction => by
        simpa [Term.substAt] using
          (Step.appLeft
            (argument := Term.substAt depth replacement argument)
            (Step.substAt reduction depth replacement))
    | @Step.appRight _ _ argument argument' function reduction => by
        simpa [Term.substAt] using
          (Step.appRight
            (function := Term.substAt depth replacement function)
            (Step.substAt reduction depth replacement))

  theorem Steps.substAt {stage term result}
      (reduction : Steps Δ stage term result) (depth : Nat) (replacement : Term) :
      Steps Δ stage (Term.substAt depth replacement term)
        (Term.substAt depth replacement result) :=
    match reduction with
    | .refl => .refl
    | .tail head tail =>
        .tail (Step.substAt head depth replacement)
          (Steps.substAt tail depth replacement)

  theorem Steps.invert_lam_source_aux {stage source result}
      (reduction : Steps Δ stage source result) :
      ∀ body, source = .lam body →
        ∃ body', result = .lam body' ∧ Steps Δ stage body body' := by
    exact Steps.rec
      (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun stage source result _ =>
        ∀ body, source = .lam body →
          ∃ body', result = .lam body' ∧ Steps Δ stage body body')
      (beta := by intros; trivial)
      (muUnfold := by intros; trivial)
      (delta := by intros; trivial)
      (starredIdempotence := by intros; trivial)
      (starChecking := by intros; trivial)
      (lam := by intros; trivial)
      (mu := by intros; trivial)
      (appLeft := by intros; trivial)
      (appRight := by intros; trivial)
      (refl := by
        intro _ _
        intro body equality
        cases equality
        exact ⟨body, rfl, .refl⟩)
      (tail := by
        intro _ _ _ _
        intro head _ _ tailHypothesis body equality
        cases equality
        obtain ⟨middleBody, rfl, bodyHead⟩ := Step.invert_lam head
        obtain ⟨resultBody, rfl, bodyTail⟩ :=
          tailHypothesis middleBody rfl
        exact ⟨resultBody, rfl, .tail bodyHead bodyTail⟩)
      reduction
end

/-- A finite reduction from a lambda remains a lambda throughout. -/
theorem Steps.invert_lam_source
    (reduction : Steps Δ stage (.lam body) result) :
    ∃ body', result = .lam body' ∧ Steps Δ stage body body' :=
  Steps.invert_lam_source_aux reduction body rfl

/-- A finite reduction between lambdas restricts to their bodies. -/
theorem Steps.invert_lam
    (reduction : Steps Δ stage (.lam body) (.lam body')) :
    Steps Δ stage body body' := by
  obtain ⟨resultBody, equality, bodyReduction⟩ :=
    Steps.invert_lam_source reduction
  cases equality
  exact bodyReduction

/-
Stage monotonicity is mutual because a star-checking step contains a
multi-step certificate from the preceding stage:

    t ↦ₙ u  ⟹  t ↦ₙ₊₁ u
    t ↦ₙ* u ⟹  t ↦ₙ₊₁* u.
-/
mutual
  theorem Step.monoSucc : Step Δ stage term result →
      Step Δ (stage + 1) term result
    | .beta => .beta
    | .muUnfold => .muUnfold
    | .delta defined => .delta defined
    | .starredIdempotence => .starredIdempotence
    | .starChecking certificate =>
        .starChecking (Steps.monoSucc certificate)
    | .lam reduction => .lam (Step.monoSucc reduction)
    | .mu reduction => .mu (Step.monoSucc reduction)
    | .appLeft reduction => .appLeft (Step.monoSucc reduction)
    | .appRight reduction => .appRight (Step.monoSucc reduction)

  theorem Steps.monoSucc : Steps Δ stage term result →
      Steps Δ (stage + 1) term result
    | .refl => .refl
    | .tail head tail =>
        .tail (Step.monoSucc head) (Steps.monoSucc tail)
end

/-- A reduction valid at stage `n` remains valid at every stage `n + k`. -/
theorem Step.monoAdd (reduction : Step Δ stage term result) (extra : Nat) :
    Step Δ (stage + extra) term result := by
  induction extra with
  | zero => simpa using reduction
  | succ extra inductionHypothesis =>
      simpa [Nat.add_assoc] using inductionHypothesis.monoSucc

/-- Multi-step reduction is likewise monotone in the certification stage. -/
theorem Steps.monoAdd (reduction : Steps Δ stage term result) (extra : Nat) :
    Steps Δ (stage + extra) term result := by
  induction extra with
  | zero => simpa using reduction
  | succ extra inductionHypothesis =>
      simpa [Nat.add_assoc] using inductionHypothesis.monoSucc

/-- Order-theoretic form of stage monotonicity: `n ≤ m → (↦ₙ) ⊆ (↦ₘ)`. -/
theorem Step.mono (reduction : Step Δ stage term result)
    (le : stage ≤ later) : Step Δ later term result := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  exact reduction.monoAdd extra

/-- Order-theoretic stage monotonicity for finite reductions. -/
theorem Steps.mono (reduction : Steps Δ stage term result)
    (le : stage ≤ later) : Steps Δ later term result := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  exact reduction.monoAdd extra

/-- A one-step reduction at some finite certification stage. -/
def ReducesOne (Δ : DefEnv) (term result : Term) : Prop :=
  ∃ stage, Step Δ stage term result

/-- A finite reduction at some finite certification stage. -/
def Reduces (Δ : DefEnv) (term result : Term) : Prop :=
  ∃ stage, Steps Δ stage term result

/--
The judgment `Δ ⊢ Idempotent u` means
`λx. u (u x) ↦* λx. u x` at some finite certification stage.
-/
def Idempotent (Δ : DefEnv) (u : Term) : Prop :=
  Reduces Δ (idempotenceLhs u) (idempotenceRhs u)

/-- A one-hole term context, used to place an assumed idempotence contraction. -/
inductive ReductionContext where
  | hole
  | lam : ReductionContext → ReductionContext
  | mu : ReductionContext → ReductionContext
  | appLeft : ReductionContext → Term → ReductionContext
  | appRight : Term → ReductionContext → ReductionContext

namespace ReductionContext

def fill : ReductionContext → Term → Term
  | .hole, term => term
  | .lam context, term => .lam (context.fill term)
  | .mu context, term => .mu (context.fill term)
  | .appLeft context argument, term => .app (context.fill term) argument
  | .appRight function context, term => .app function (context.fill term)

/-- Number of binders crossed on the path to the hole. -/
def binders : ReductionContext → Nat
  | .hole => 0
  | .lam context => context.binders + 1
  | .mu context => context.binders + 1
  | .appLeft context _ => context.binders
  | .appRight _ context => context.binders

def substAt (depth : Nat) (replacement : Term) :
    ReductionContext → ReductionContext
  | .hole => .hole
  | .lam context => .lam (context.substAt (depth + 1) replacement)
  | .mu context => .mu (context.substAt (depth + 1) replacement)
  | .appLeft context argument =>
      .appLeft (context.substAt depth replacement)
        (Term.substAt depth replacement argument)
  | .appRight function context =>
      .appRight (Term.substAt depth replacement function)
        (context.substAt depth replacement)

theorem substAt_binders (context : ReductionContext) :
    (context.substAt depth replacement).binders = context.binders := by
  induction context generalizing depth with
  | hole => rfl
  | lam context inductionHypothesis =>
      simp [substAt, binders, inductionHypothesis]
  | mu context inductionHypothesis =>
      simp [substAt, binders, inductionHypothesis]
  | appLeft context argument inductionHypothesis =>
      simp [substAt, binders, inductionHypothesis]
  | appRight function context inductionHypothesis =>
      simp [substAt, binders, inductionHypothesis]

theorem substAt_fill (context : ReductionContext) (term replacement : Term)
    (depth : Nat) :
    Term.substAt depth replacement (context.fill term) =
      (context.substAt depth replacement).fill
        (Term.substAt (depth + context.binders) replacement term) := by
  induction context generalizing depth with
  | hole => simp [fill, substAt, binders]
  | lam context inductionHypothesis =>
      simpa [fill, substAt, binders, Term.substAt, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (depth := depth + 1)
  | mu context inductionHypothesis =>
      simpa [fill, substAt, binders, Term.substAt, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (depth := depth + 1)
  | appLeft context argument inductionHypothesis =>
      simp [fill, substAt, binders, Term.substAt, inductionHypothesis]
  | appRight function context inductionHypothesis =>
      simp [fill, substAt, binders, Term.substAt, inductionHypothesis]

end ReductionContext

/--
One ordinary reduction, an assumed idempotence contraction, or an
assumption-scoped μ-fold in an arbitrary context. Folding is available only
for a recursive projector already present in the induction assumptions; it is
not part of ordinary runtime reduction.
-/
def AssumedStep (Δ : DefEnv) (assumptions : List Term) (stage : Nat)
    (term result : Term) : Prop :=
  Step Δ stage term result ∨
    (∃ (context : ReductionContext) (projector argument : Term),
        projector ∈ assumptions ∧
        let shifted := projector.shift context.binders 0
        term = context.fill (.app shifted (.app shifted argument)) ∧
        result = context.fill (.app shifted argument)) ∨
    ∃ (context : ReductionContext) (body : Term),
      .mu body ∈ assumptions ∧
      let shiftedBody := body.shift context.binders 1
      term = context.fill shiftedBody.unfoldMu ∧
      result = context.fill (.mu shiftedBody)

/-- Reflexive-transitive closure of reduction under idempotence assumptions. -/
inductive AssumedSteps (Δ : DefEnv) (assumptions : List Term) :
    Nat → Term → Term → Prop where
  | refl : AssumedSteps Δ assumptions stage term term
  | tail : AssumedStep Δ assumptions stage term middle →
      AssumedSteps Δ assumptions stage middle result →
      AssumedSteps Δ assumptions stage term result

namespace AssumedSteps

theorem single (step : AssumedStep Δ assumptions stage term result) :
    AssumedSteps Δ assumptions stage term result :=
  .tail step .refl

end AssumedSteps

theorem AssumedStep.monoSucc :
    AssumedStep Δ assumptions stage term result →
      AssumedStep Δ assumptions (stage + 1) term result
  | Or.inl reduction => Or.inl (Step.monoSucc reduction)
  | Or.inr assumed => Or.inr assumed

theorem AssumedSteps.monoSucc
    (reduction : AssumedSteps Δ assumptions stage term result) :
    AssumedSteps Δ assumptions (stage + 1) term result := by
  induction reduction with
  | refl => exact .refl
  | tail head tail inductionHypothesis =>
      exact .tail (AssumedStep.monoSucc head) inductionHypothesis

/--
Under the equi-recursive hypothesis for `μX.F(X)`, its unfolding is
idempotent: fold both copies, contract by the hypothesis, then unfold the
remaining copy.
-/
theorem unfoldMu_idempotentAssumingMu (Δ : DefEnv) (stage : Nat) (body : Term) :
  AssumedSteps Δ [Term.mu body] stage
      (idempotenceLhs body.unfoldMu) (idempotenceRhs body.unfoldMu) := by
  let shiftedBody := body.shift 1 1
  let unfolded := shiftedBody.unfoldMu
  let recursive : Term := (Term.mu body).shift 1 0
  have shiftUnfolded : body.unfoldMu.shift 1 0 = unfolded := by
    simpa [unfolded, shiftedBody, Term.unfoldMu, Term.shift] using
      shift_instantiate body (Term.mu body) 1 0
  rw [idempotenceLhs, idempotenceRhs, shiftUnfolded]
  have foldOuter : AssumedStep Δ [Term.mu body] stage
      (.lam (.app unfolded (.app unfolded (.bvar 0))))
      (.lam (.app recursive (.app unfolded (.bvar 0)))) := by
    apply Or.inr
    apply Or.inr
    refine ⟨.lam (.appLeft .hole (.app unfolded (.bvar 0))), body, by simp, ?_⟩
    simp [ReductionContext.binders, ReductionContext.fill, shiftedBody,
      unfolded, recursive, Term.shift]
  have foldInner : AssumedStep Δ [Term.mu body] stage
      (.lam (.app recursive (.app unfolded (.bvar 0))))
      (.lam (.app recursive (.app recursive (.bvar 0)))) := by
    apply Or.inr
    apply Or.inr
    refine ⟨.lam (.appRight recursive (.appLeft .hole (.bvar 0))), body,
      by simp, ?_⟩
    simp [ReductionContext.binders, ReductionContext.fill, shiftedBody,
      unfolded, recursive, Term.shift]
  have contract : AssumedStep Δ [Term.mu body] stage
      (.lam (.app recursive (.app recursive (.bvar 0))))
      (.lam (.app recursive (.bvar 0))) := by
    apply Or.inr
    apply Or.inl
    refine ⟨.lam .hole, Term.mu body, .bvar 0, by simp, ?_⟩
    simp [ReductionContext.binders, ReductionContext.fill, recursive]
  have unfoldFinal : AssumedStep Δ [Term.mu body] stage
      (.lam (.app recursive (.bvar 0)))
      (.lam (.app unfolded (.bvar 0))) := by
    apply Or.inl
    simpa [recursive, Term.shift] using
      (Step.lam (Step.appLeft (argument := .bvar 0)
        (Step.muUnfold (Δ := Δ) (stage := stage) (body := shiftedBody))))
  exact .tail foldOuter (.tail foldInner (.tail contract (.tail unfoldFinal .refl)))

/--
Proof objects for idempotence with explicit recursive hypotheses.

`admissible body` is deliberately a parameter: instantiating it requires a
separate positivity, monotonicity, or guardedness argument. Thus `mu` exposes
the induction principle without making every untyped recursive body sound.
-/
inductive InductiveIdempotent (Δ : DefEnv) (admissible : Term → Prop) :
    List Term → Nat → Term → Prop where
  | hypothesis (membership : term ∈ assumptions) :
      InductiveIdempotent Δ admissible assumptions stage term
  | finite (certificate : Steps Δ stage
      (idempotenceLhs term) (idempotenceRhs term)) :
      InductiveIdempotent Δ admissible assumptions stage term
  | underAssumptions (certificate : AssumedSteps Δ assumptions stage
      (idempotenceLhs term) (idempotenceRhs term)) :
      InductiveIdempotent Δ admissible assumptions stage term
  | mu (accepted : admissible body)
      (bodyCertificate : InductiveIdempotent Δ admissible
        (.mu body :: assumptions) stage body.unfoldMu) :
      InductiveIdempotent Δ admissible assumptions stage (.mu body)

theorem InductiveIdempotent.monoSucc :
    InductiveIdempotent Δ admissible assumptions stage term →
      InductiveIdempotent Δ admissible assumptions (stage + 1) term
  | .hypothesis membership => .hypothesis membership
  | .finite certificate => .finite certificate.monoSucc
  | .underAssumptions certificate => .underAssumptions certificate.monoSucc
  | .mu accepted bodyCertificate => .mu accepted bodyCertificate.monoSucc

/-- A closed inductive idempotence proof at some finite stage. -/
def IdempotentByInduction (Δ : DefEnv) (admissible : Term → Prop)
    (term : Term) : Prop :=
  ∃ stage, InductiveIdempotent Δ admissible [] stage term

/-- Inductive idempotence using the concrete star-guarded μ criterion. -/
abbrev GuardedInductiveIdempotent (Δ : DefEnv) :=
  InductiveIdempotent Δ Term.MuBodyGuarded

/-- Every guarded μ body has a closed inductive idempotence certificate. -/
theorem guardedMu_inductivelyIdempotent
    (accepted : body.MuBodyGuarded) :
    GuardedInductiveIdempotent Δ [] stage (.mu body) := by
  apply InductiveIdempotent.mu accepted
  apply InductiveIdempotent.underAssumptions
  exact unfoldMu_idempotentAssumingMu Δ stage body

/-- A closed-assumption guarded proof at some finite stage. -/
def GuardedIdempotentByInduction (Δ : DefEnv) (term : Term) : Prop :=
  ∃ stage, GuardedInductiveIdempotent Δ [] stage term

/-- A closed projector carrying a guarded inductive certificate. -/
def InductivelyCertified (Δ : DefEnv) (stage : Nat) (term : Term) : Prop :=
  term.Closed ∧ GuardedInductiveIdempotent Δ [] stage term

/--
Reduction extended with contextual guarded star-checking and the idempotence
contraction justified by the same certificate.
-/
def ExtendedStep (Δ : DefEnv) (stage : Nat) (term result : Term) : Prop :=
  Step Δ stage term result ∨
    (∃ (context : ReductionContext) (prior : Nat) (u : Term),
        stage = prior + 1 ∧
        term = context.fill (.app .star u) ∧
        result = context.fill u ∧
        InductivelyCertified Δ prior u) ∨
    ∃ (context : ReductionContext) (prior : Nat) (u argument : Term),
      stage = prior + 1 ∧
      term = context.fill (.app u (.app u argument)) ∧
      result = context.fill (.app u argument) ∧
      InductivelyCertified Δ prior u

/-- Reflexive-transitive closure of the extended reduction. -/
inductive ExtendedSteps (Δ : DefEnv) : Nat → Term → Term → Prop where
  | refl : ExtendedSteps Δ stage term term
  | tail : ExtendedStep Δ stage term middle →
      ExtendedSteps Δ stage middle result →
      ExtendedSteps Δ stage term result

namespace ExtendedSteps

theorem single (step : ExtendedStep Δ stage term result) :
    ExtendedSteps Δ stage term result :=
  .tail step .refl

end ExtendedSteps

/-- A guarded closed inductive proof licenses `* u ↦ u` one stage later. -/
theorem inductiveStarChecking
    (closed : u.Closed)
    (certificate : GuardedInductiveIdempotent Δ [] stage u) :
    ExtendedStep Δ (stage + 1) (.app .star u) u := by
  exact Or.inr (Or.inl
    ⟨.hole, stage, u, rfl, rfl, rfl, closed, certificate⟩)

/-- A guarded closed certificate contracts `u (u t)` contextually. -/
theorem inductiveIdempotence
    (closed : u.Closed)
    (certificate : GuardedInductiveIdempotent Δ [] stage u) :
    ExtendedStep Δ (stage + 1) (.app u (.app u term)) (.app u term) := by
  exact Or.inr (Or.inr
    ⟨.hole, stage, u, term, rfl, rfl, rfl, closed, certificate⟩)

theorem ExtendedStep.monoSucc
    (reduction : ExtendedStep Δ stage term result) :
    ExtendedStep Δ (stage + 1) term result := by
  rcases reduction with ordinary | assumed
  · exact Or.inl ordinary.monoSucc
  rcases assumed with checking | idempotence
  · rcases checking with ⟨context, prior, u, rfl, rfl, rfl, closed, certificate⟩
    exact Or.inr (Or.inl ⟨context, prior + 1, u, by omega, rfl, rfl,
      closed, certificate.monoSucc⟩)
  · rcases idempotence with
      ⟨context, prior, u, argument, rfl, rfl, rfl, closed, certificate⟩
    exact Or.inr (Or.inr ⟨context, prior + 1, u, argument, by omega, rfl, rfl,
      closed, certificate.monoSucc⟩)

theorem ExtendedSteps.monoSucc
    (reduction : ExtendedSteps Δ stage term result) :
    ExtendedSteps Δ (stage + 1) term result := by
  induction reduction with
  | refl => exact .refl
  | tail head tail inductionHypothesis =>
      exact .tail head.monoSucc inductionHypothesis

theorem ExtendedStep.monoAdd
    (reduction : ExtendedStep Δ stage term result) (extra : Nat) :
    ExtendedStep Δ (stage + extra) term result := by
  induction extra with
  | zero => simpa using reduction
  | succ extra inductionHypothesis =>
      simpa [Nat.add_assoc] using inductionHypothesis.monoSucc

theorem ExtendedSteps.monoAdd
    (reduction : ExtendedSteps Δ stage term result) (extra : Nat) :
    ExtendedSteps Δ (stage + extra) term result := by
  induction extra with
  | zero => simpa using reduction
  | succ extra inductionHypothesis =>
      simpa [Nat.add_assoc] using inductionHypothesis.monoSucc

theorem ExtendedStep.mono
    (reduction : ExtendedStep Δ stage term result) (le : stage ≤ later) :
    ExtendedStep Δ later term result := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  exact reduction.monoAdd extra

theorem ExtendedSteps.mono
    (reduction : ExtendedSteps Δ stage term result) (le : stage ≤ later) :
    ExtendedSteps Δ later term result := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  exact reduction.monoAdd extra

theorem ExtendedStep.substAt
    (reduction : ExtendedStep Δ stage term result)
    (depth : Nat) (replacement : Term) :
    ExtendedStep Δ stage (Term.substAt depth replacement term)
      (Term.substAt depth replacement result) := by
  rcases reduction with ordinary | assumed
  · exact Or.inl (Step.substAt ordinary depth replacement)
  rcases assumed with checking | idempotence
  · rcases checking with
      ⟨context, prior, u, stageEquality, rfl, rfl, closed, certificate⟩
    have unchanged : Term.substAt (depth + context.binders) replacement u = u :=
      Term.substAt_eq_self_of_wellScoped
        (replacement := replacement) (closed.mono (Nat.zero_le _))
    refine Or.inr (Or.inl
      ⟨context.substAt depth replacement, prior, u, stageEquality, ?_, ?_,
        closed, certificate⟩)
    · rw [ReductionContext.substAt_fill]
      simp [Term.substAt, unchanged]
    · rw [ReductionContext.substAt_fill]
      exact congrArg (context.substAt depth replacement).fill unchanged
  · rcases idempotence with
      ⟨context, prior, u, argument, stageEquality, rfl, rfl, closed, certificate⟩
    let holeDepth := depth + context.binders
    let argument' := Term.substAt holeDepth replacement argument
    have unchanged : Term.substAt holeDepth replacement u = u :=
      Term.substAt_eq_self_of_wellScoped
        (replacement := replacement) (closed.mono (Nat.zero_le _))
    refine Or.inr (Or.inr
      ⟨context.substAt depth replacement, prior, u, argument', stageEquality,
        ?_, ?_, closed, certificate⟩)
    · rw [ReductionContext.substAt_fill]
      simp [Term.substAt, holeDepth, argument', unchanged]
    · rw [ReductionContext.substAt_fill]
      simp [Term.substAt, holeDepth, argument', unchanged]

theorem ExtendedSteps.substAt
    (reduction : ExtendedSteps Δ stage term result)
    (depth : Nat) (replacement : Term) :
    ExtendedSteps Δ stage (Term.substAt depth replacement term)
      (Term.substAt depth replacement result) := by
  induction reduction with
  | refl => exact .refl
  | tail head tail inductionHypothesis =>
      exact .tail (head.substAt depth replacement) inductionHypothesis

/-- The new star-checking/starred-idempotence critical peak is joinable. -/
theorem inductiveStarChecking_starredIdempotence_peak
    (closed : u.Closed)
    (certificate : GuardedInductiveIdempotent Δ [] stage u) :
    ∃ common,
      ExtendedSteps Δ (stage + 1) (.app (.app .star u) term) common ∧
      ExtendedSteps Δ (stage + 1) (.app u (.app (.app .star u) term)) common := by
  refine ⟨.app u term, ?_, ?_⟩
  · exact ExtendedSteps.single (Or.inr (Or.inl
      ⟨.appLeft .hole term, stage, u, rfl, rfl, rfl, closed, certificate⟩))
  · exact .tail
      (Or.inr (Or.inl
        ⟨.appRight u (.appLeft .hole term), stage, u, rfl, rfl, rfl,
          closed, certificate⟩))
      (ExtendedSteps.single (inductiveIdempotence closed certificate))

/-- A minimal closed recursive projector used to exercise the induction rule. -/
def muIdentity : Term :=
  .mu (.lam (.bvar 0))

theorem muIdentity_inductivelyIdempotent (Δ : DefEnv) :
    GuardedInductiveIdempotent Δ [] 0 muIdentity := by
  apply InductiveIdempotent.mu (by native_decide)
  apply InductiveIdempotent.finite
  simpa [muIdentity, Term.unfoldMu, Term.instantiate, Term.substAt,
    idempotenceLhs, idempotenceRhs, Term.shift] using
    (Steps.single (Δ := Δ) (Step.lam (Step.beta
      (body := .bvar 0) (argument := .app (.lam (.bvar 0)) (.bvar 0)))))

theorem star_muIdentity (Δ : DefEnv) :
    ExtendedStep Δ 1 (.app .star muIdentity) muIdentity := by
  apply inductiveStarChecking (by native_decide)
  exact muIdentity_inductivelyIdempotent Δ

/-- The displayed star-checking rule, with its stage hidden existentially. -/
theorem starChecking (certificate : Idempotent Δ u) :
    ReducesOne Δ (.app .star u) u := by
  obtain ⟨stage, derivation⟩ := certificate
  exact ⟨stage + 1, .starChecking derivation⟩

/-- Star application is idempotent: `Δ ⊢ Idempotent (* u)`. -/
theorem starApp_idempotent (Δ : DefEnv) (u : Term) :
    Idempotent Δ (.app .star u) := by
  exact ⟨0, Steps.single (.lam .starredIdempotence)⟩

/-- The first derived law from the paper: `* (* u) ↦ * u`. -/
theorem star_starApp (Δ : DefEnv) (u : Term) :
    ReducesOne Δ (.app .star (.app .star u)) (.app .star u) :=
  starChecking (starApp_idempotent Δ u)

/-- The star constant is itself idempotent: `Δ ⊢ Idempotent *`. -/
theorem star_idempotent (Δ : DefEnv) : Idempotent Δ .star := by
  have certificate : Steps Δ 0
      (idempotenceLhs (.app .star (.bvar 0)))
      (idempotenceRhs (.app .star (.bvar 0))) :=
    Steps.single (.lam .starredIdempotence)
  exact ⟨1, Steps.single (.lam (.starChecking certificate))⟩

/-- The second derived law from the paper: `* * ↦ *`. -/
theorem star_star (Δ : DefEnv) : ReducesOne Δ (.app .star .star) .star :=
  starChecking (star_idempotent Δ)

end LambdaStar
