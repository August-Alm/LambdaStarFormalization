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
    /-- A closure unfolds only when applied: `c u ↦ Δ(c) u`. -/
    | delta (defined : Δ.defs name = some body) :
      Step Δ stage (.app (.const name) argument) (.app body argument)
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

/-- A bare closure name is a stable identity; only applications unfold. -/
theorem Step.no_const_source (reduction : Step Δ stage (.const name) result) :
    False := by
  cases reduction

/-- Finite reduction cannot change a bare closure name. -/
theorem Steps.const_source
    (reduction : Steps Δ stage (.const name) result) :
    result = .const name := by
  cases reduction with
  | refl => rfl
  | tail head _ => exact False.elim head.no_const_source

/-- Applying a defined closure exposes its body at the same argument. -/
theorem Steps.unfoldClosure (defined : Δ.defs name = some body) :
    Steps Δ stage (.app (.const name) argument) (.app body argument) :=
  .single (.delta defined)

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
    | @Step.delta _ _ body name argument defined => by
        have hClosed := Δ.closed _ _ defined
        have hBody : Term.substAt depth replacement body = body :=
          Term.substAt_eq_self_of_wellScoped
            (replacement := replacement) (hClosed.mono (Nat.zero_le depth))
        simpa [Term.substAt, hBody] using
          (Step.delta (Δ := Δ) (argument := Term.substAt depth replacement argument)
            defined)
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
      (delta := by intros; trivial)
      (starredIdempotence := by intros; trivial)
      (starChecking := by intros; trivial)
      (lam := by intros; trivial)
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
    | .delta defined => .delta defined
    | .starredIdempotence => .starredIdempotence
    | .starChecking certificate =>
        .starChecking (Steps.monoSucc certificate)
    | .lam reduction => .lam (Step.monoSucc reduction)
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

/--
Find one leftmost computational contraction and return its reduction proof.
Besides the unconditional rules, this executable fragment includes delta and
the two generic star laws already certified above.
-/
def computationalStep (Δ : DefEnv) (stage : Nat) :
    (term : Term) → Option { result // Step Δ stage term result }
  | .bvar _ => none
  | .const _ => none
  | .star => none
  | .lam body =>
      match computationalStep Δ stage body with
      | none => none
      | some ⟨body', reduction⟩ => some ⟨.lam body', .lam reduction⟩
  | .app (.lam body) argument =>
      some ⟨body.instantiate argument, .beta⟩
  | .app .star .star =>
      if sufficient : 2 ≤ stage then
        have inner : Steps Δ 0
            (idempotenceLhs (.app .star (.bvar 0)))
            (idempotenceRhs (.app .star (.bvar 0))) :=
          Steps.single (.lam .starredIdempotence)
        have certificate : Steps Δ 1
            (idempotenceLhs .star) (idempotenceRhs .star) :=
          Steps.single (.lam (.starChecking inner))
        some ⟨.star, (Step.starChecking certificate).mono sufficient⟩
      else none
  | .app .star (.app .star u) =>
      if sufficient : 1 ≤ stage then
        have certificate : Steps Δ 0
            (idempotenceLhs (.app .star u))
            (idempotenceRhs (.app .star u)) :=
          Steps.single (.lam .starredIdempotence)
        some ⟨.app .star u, (Step.starChecking certificate).mono sufficient⟩
      else none
  | .app (.const name) argument =>
      match defined : Δ.defs name with
      | none => none
      | some body => some ⟨.app body argument, .delta defined⟩
  | .app (.app .star u) (.app (.app .star u') term) =>
      if equality : u = u' then
        some ⟨.app (.app .star u) term, by
          subst u'
          exact .starredIdempotence⟩
      else
        match computationalStep Δ stage (.app .star u) with
        | some ⟨function', reduction⟩ =>
            some ⟨.app function' (.app (.app .star u') term),
              .appLeft reduction⟩
        | none =>
            match computationalStep Δ stage (.app (.app .star u') term) with
            | none => none
            | some ⟨argument', reduction⟩ =>
                some ⟨.app (.app .star u) argument', .appRight reduction⟩
  | .app function argument =>
      match computationalStep Δ stage function with
      | some ⟨function', reduction⟩ =>
          some ⟨.app function' argument, .appLeft reduction⟩
      | none =>
          match computationalStep Δ stage argument with
          | none => none
          | some ⟨argument', reduction⟩ =>
              some ⟨.app function argument', .appRight reduction⟩

/-- A fuel-bounded run of `computationalStep`, carrying its full certificate. -/
def computationalSteps (Δ : DefEnv) (stage : Nat) :
    (fuel : Nat) → (term : Term) → { result // Steps Δ stage term result }
  | 0, term => ⟨term, .refl⟩
  | fuel + 1, term =>
      match computationalStep Δ stage term with
      | none => ⟨term, .refl⟩
      | some ⟨middle, head⟩ =>
          let tail := computationalSteps Δ stage fuel middle
          ⟨tail.1, .tail head tail.2⟩

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
  | appLeft : ReductionContext → Term → ReductionContext
  | appRight : Term → ReductionContext → ReductionContext

namespace ReductionContext

def fill : ReductionContext → Term → Term
  | .hole, term => term
  | .lam context, term => .lam (context.fill term)
  | .appLeft context argument, term => .app (context.fill term) argument
  | .appRight function context, term => .app function (context.fill term)

/-- Number of binders crossed on the path to the hole. -/
def binders : ReductionContext → Nat
  | .hole => 0
  | .lam context => context.binders + 1
  | .appLeft context _ => context.binders
  | .appRight _ context => context.binders

def substAt (depth : Nat) (replacement : Term) :
    ReductionContext → ReductionContext
  | .hole => .hole
  | .lam context => .lam (context.substAt (depth + 1) replacement)
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
  | appLeft context argument inductionHypothesis =>
      simp [fill, substAt, binders, Term.substAt, inductionHypothesis]
  | appRight function context inductionHypothesis =>
      simp [fill, substAt, binders, Term.substAt, inductionHypothesis]

end ReductionContext

/-- One-step reduction is closed under every reduction context. -/
theorem Step.inContext (context : ReductionContext)
  (reduction : Step Δ stage left right) :
  Step Δ stage (context.fill left) (context.fill right) := by
  induction context with
  | hole => exact reduction
  | lam context inductionHypothesis => exact .lam inductionHypothesis
  | appLeft context argument inductionHypothesis =>
    exact .appLeft inductionHypothesis
  | appRight function context inductionHypothesis =>
    exact .appRight inductionHypothesis

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
