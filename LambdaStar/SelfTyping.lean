import LambdaStar.Confluence

namespace LambdaStar

/-- Scoped operational equations available while checking a term. -/
abbrev TypingContext := List (Term × Term)

namespace TypingContext

/-- Move an equation under one fresh binder. -/
def shiftEquation (equation : Term × Term) : Term × Term :=
  (equation.1.shift 1 0, equation.2.shift 1 0)

/-- Bind a fresh variable `u : type`, contributing `type u ≃ u`. -/
def bind (context : TypingContext) (type : Term) : TypingContext :=
  (.app (type.shift 1 0) (.bvar 0), .bvar 0) ::
    context.map shiftEquation

end TypingContext

/-- Equational reasoning under scoped typing assumptions. -/
inductive ContextEquiv (Δ : DefEnv) : TypingContext → Term → Term → Prop where
  | operational : Joinable Δ left right → ContextEquiv Δ context left right
  | assumption (membership : (left, right) ∈ context) :
    ContextEquiv Δ context left right
  | refl : ContextEquiv Δ context term term
  | symm : ContextEquiv Δ context left right → ContextEquiv Δ context right left
  | trans : ContextEquiv Δ context left middle →
    ContextEquiv Δ context middle right → ContextEquiv Δ context left right
  | lam : ContextEquiv Δ (context.map TypingContext.shiftEquation) body body' →
    ContextEquiv Δ context (.lam body) (.lam body')
  | appLeft : ContextEquiv Δ context function function' →
    ContextEquiv Δ context (.app function argument) (.app function' argument)
  | appRight : ContextEquiv Δ context argument argument' →
    ContextEquiv Δ context (.app function argument) (.app function argument')
  | funext :
      ContextEquiv Δ (context.map TypingContext.shiftEquation)
        (.app (left.shift 1 0) (.bvar 0))
        (.app (right.shift 1 0) (.bvar 0)) →
      ContextEquiv Δ context left right
  | starChecking :
        ContextEquiv Δ context (idempotenceLhs term) (idempotenceRhs term) →
        ContextEquiv Δ context (.app .star term) term
  /--
  Guarded cyclic idempotence for a recursive closure. The recursive hypothesis
  `x : A` is available only after the environment identifies `A` with a
  self-indexed family, while checking that unfolded family.
  -/
  | recursiveIdempotence
      (defined : Δ.defs name = some (Term.self family))
      (guarded : ContextEquiv Δ
        (TypingContext.bind
          ((.app .star (.const name), .const name) :: context) (.const name))
        (.app .star family) family) :
      ContextEquiv Δ context
        (idempotenceLhs (.const name)) (idempotenceRhs (.const name))

namespace ContextEquiv

/-- Every one-step reduction is valid contextual equality. -/
theorem ofStep (reduction : Step Δ stage left right) :
  ContextEquiv Δ context left right :=
  .operational ⟨right, ⟨stage, .single reduction⟩, ⟨0, .refl⟩⟩

/-- A scoped equation `* A ≃ A` makes `A` an idempotent projector. -/
theorem idempotentOn
    (isType : ContextEquiv Δ context (.app .star type) type) (term : Term) :
    ContextEquiv Δ context (.app type (.app type term)) (.app type term) := by
  exact .trans
    (.appLeft (.symm isType))
    (.trans
      (.appRight (.appLeft (.symm isType)))
      (.trans
        (ofStep (Step.starredIdempotence (stage := 0)))
        (.appLeft isType)))

/-- Find the first scoped equation whose left side is the requested term. -/
def lookupEquation :
    (context : TypingContext) → (term : Term) →
      Option { result // (term, result) ∈ context }
  | [], _ => none
  | equation :: context, term =>
      if equality : term = equation.1 then
        some ⟨equation.2, by
          subst term
          exact .head context⟩
      else
        match lookupEquation context term with
        | none => none
        | some ⟨result, membership⟩ =>
            some ⟨result, .tail equation membership⟩

/-- Use the first scoped equation whose left side is the requested term. -/
def assumptionStep (Δ : DefEnv) (context : TypingContext) (term : Term) :
    Option { result // ContextEquiv Δ context term result } :=
  match lookupEquation context term with
  | none => none
  | some ⟨result, membership⟩ => some ⟨result, .assumption membership⟩

/--
One leftmost contextual contraction, carrying its equality proof. It uses no
cyclic premise: every non-operational contraction comes from an explicit
scoped equation.
-/
def contextualStep (Δ : DefEnv) (context : TypingContext) :
    (term : Term) → Option { result // ContextEquiv Δ context term result }
  | .bvar index => assumptionStep Δ context (.bvar index)
  | .const name => assumptionStep Δ context (.const name)
  | .star => assumptionStep Δ context .star
  | .lam body =>
    match assumptionStep Δ context (.lam body) with
    | some step => some step
    | none =>
      match contextualStep Δ
        (context.map TypingContext.shiftEquation) body with
      | none => none
      | some ⟨body', proof⟩ =>
        some ⟨.lam body', ContextEquiv.lam (context := context) proof⟩
  | .app (.lam body) argument =>
    match assumptionStep Δ context (.app (.lam body) argument) with
    | some step => some step
      | none => some ⟨body.instantiate argument, by
        have reduction : Step Δ 0 (.app (.lam body) argument)
          (body.instantiate argument) := .beta
        exact ofStep (context := context) reduction⟩
  | Term.app Term.star Term.star =>
    match assumptionStep Δ context (.app .star .star) with
    | some step => some step
    | none => some ⟨.star, by
      obtain ⟨stage, reduction⟩ := star_star Δ
      exact ofStep (context := context) reduction⟩
  | Term.app Term.star (Term.app Term.star type) =>
    match assumptionStep Δ context (.app .star (.app .star type)) with
    | some step => some step
    | none => some ⟨.app .star type, by
      obtain ⟨stage, reduction⟩ := star_starApp Δ type
      exact ofStep (context := context) reduction⟩
  | .app (.app .star type) (.app (.app .star type') argument) =>
    match assumptionStep Δ context
      (.app (.app .star type) (.app (.app .star type') argument)) with
    | some step => some step
    | none =>
      if equality : type = type' then
      some ⟨.app (.app .star type) argument, by
        subst type'
        have reduction : Step Δ 0
            (.app (.app .star type) (.app (.app .star type) argument))
            (.app (.app .star type) argument) := .starredIdempotence
        exact ofStep (context := context) reduction⟩
      else
      match contextualStep Δ context (.app .star type) with
      | some ⟨function', proof⟩ =>
        some ⟨.app function' (.app (.app .star type') argument),
          .appLeft proof⟩
      | none =>
        match contextualStep Δ context
          (.app (.app .star type') argument) with
        | none => none
        | some ⟨argument', proof⟩ =>
          some ⟨.app (.app .star type) argument', .appRight proof⟩
  | .app type (.app type' argument) =>
    match assumptionStep Δ context (.app type (.app type' argument)) with
    | some step => some step
    | none =>
      if equality : type = type' then
      if membership : (.app .star type, type) ∈ context then
        some ⟨.app type argument, by
        subst type'
        exact idempotentOn (Δ := Δ) (context := context)
          (.assumption membership) argument⟩
      else
        match contextualStep Δ context type with
        | some ⟨type'', proof⟩ =>
          some ⟨.app type'' (.app type' argument), .appLeft proof⟩
        | none =>
          match contextualStep Δ context (.app type' argument) with
          | none => none
          | some ⟨argument', proof⟩ =>
            some ⟨.app type argument', .appRight proof⟩
      else
      match contextualStep Δ context type with
      | some ⟨type'', proof⟩ =>
        some ⟨.app type'' (.app type' argument), .appLeft proof⟩
      | none =>
        match contextualStep Δ context (.app type' argument) with
        | none => none
        | some ⟨argument', proof⟩ =>
          some ⟨.app type argument', .appRight proof⟩
  | .app function argument =>
    match assumptionStep Δ context (.app function argument) with
    | some step => some step
    | none =>
      match contextualStep Δ context function with
      | some ⟨function', proof⟩ =>
        some ⟨.app function' argument, .appLeft proof⟩
      | none =>
        match contextualStep Δ context argument with
        | none => none
        | some ⟨argument', proof⟩ =>
          some ⟨.app function argument', .appRight proof⟩

/-- Fuel-bounded contextual normalization with a composed equality proof. -/
def contextualSteps (Δ : DefEnv) (context : TypingContext) :
    (fuel : Nat) → (term : Term) →
      { result // ContextEquiv Δ context term result }
  | 0, term => ⟨term, .refl⟩
  | fuel + 1, term =>
      match contextualStep Δ context term with
      | none => ⟨term, .refl⟩
      | some ⟨middle, head⟩ =>
          let tail := contextualSteps Δ context fuel middle
          ⟨tail.1, .trans head tail.2⟩

/-- Equal computed contextual normal forms give a contextual equality. -/
theorem ofContextualStepsEq (fuel : Nat)
    (equality :
      (contextualSteps Δ context fuel right).1 =
        (contextualSteps Δ context fuel left).1) :
    ContextEquiv Δ context left right := by
  let leftReduction := contextualSteps Δ context fuel left
  let rightReduction := contextualSteps Δ context fuel right
  have tail : ContextEquiv Δ context leftReduction.1 right := by
    change rightReduction.1 = leftReduction.1 at equality
    rw [← equality]
    exact .symm rightReduction.2
  exact .trans leftReduction.2 tail

end ContextEquiv

/-- `Checks Γ t A` is a proof-producing operational typing derivation. -/
inductive Checks (Δ : DefEnv) : TypingContext → Term → Term → Prop where
  | certified (certificate : ContextEquiv Δ context (.app type term) term) :
    Checks Δ context term type
  | conversion
      (premise : Checks Δ context term sourceType)
      (equality : ContextEquiv Δ context sourceType targetType) :
      Checks Δ context term targetType

/-- Every self-typing derivation denotes projector equality. -/
theorem Checks.sound : Checks Δ context term type →
  ContextEquiv Δ context (.app type term) term
  | .certified certificate => certificate
  | @Checks.conversion _ context term sourceType targetType premise equality => by
      exact .trans (.appLeft (.symm equality)) premise.sound

end LambdaStar
