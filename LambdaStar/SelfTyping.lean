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

/-
Directed contextual reduction indexed by recursive observation depth. Legacy
reductions retain their independent certification stage. Depth zero is the
trivial base world used to close guarded induction.
-/
mutual
  inductive GuardedStep (prior formation : DefEnv) :
      Nat → TypingContext → Term → Term → Prop where
    | zero : GuardedStep prior formation 0 context left right
    | legacy (reduction : Step prior stage left right) :
        GuardedStep prior formation depth context left right
    | assumption (membership : (left, right) ∈ context) :
        GuardedStep prior formation depth context left right
    | idempotent
        (membership : (.app .star type, type) ∈ context) :
        GuardedStep prior formation depth context
          (.app type (.app type term)) (.app type term)
    | recursiveIdempotence
        (defined : formation.defs name = some body)
        (certificate : GuardedSteps prior formation depth
          (TypingContext.bind
            ((.app .star (.const name), .const name) ::
              (idempotenceLhs (.const name), idempotenceRhs (.const name)) ::
              context)
            (.const name))
          (.app (body.shift 1 0) (.app (.const name) (.bvar 0)))
          (.app (body.shift 1 0) (.bvar 0))) :
        GuardedStep prior formation (depth + 1) context
          (idempotenceLhs (.const name)) (idempotenceRhs (.const name))
    | starChecking
        (certificate : GuardedSteps prior formation depth context
          (idempotenceLhs term) (idempotenceRhs term)) :
        GuardedStep prior formation depth context (.app .star term) term
    | lam : GuardedStep prior formation depth
        (context.map TypingContext.shiftEquation) body body' →
        GuardedStep prior formation depth context (.lam body) (.lam body')
    | appLeft : GuardedStep prior formation depth context function function' →
        GuardedStep prior formation depth context
          (.app function argument) (.app function' argument)
    | appRight : GuardedStep prior formation depth context argument argument' →
        GuardedStep prior formation depth context
          (.app function argument) (.app function argument')

  /-- Reflexive-transitive guarded reduction at one depth and context. -/
  inductive GuardedSteps (prior formation : DefEnv) :
      Nat → TypingContext → Term → Term → Prop where
    | refl : GuardedSteps prior formation depth context term term
    | tail : GuardedStep prior formation depth context term middle →
        GuardedSteps prior formation depth context middle result →
        GuardedSteps prior formation depth context term result
end

namespace GuardedSteps

theorem single (step : GuardedStep prior formation depth context term result) :
    GuardedSteps prior formation depth context term result :=
  .tail step .refl

theorem trans :
    GuardedSteps prior formation depth context left middle →
    GuardedSteps prior formation depth context middle right →
    GuardedSteps prior formation depth context left right
  | .refl, continuation => continuation
  | .tail head continuation, rest =>
      .tail head (trans continuation rest)

/-- Embed an ordinary validated reduction without changing its stage. -/
theorem ofSteps : Steps prior stage left right →
    GuardedSteps prior formation depth context left right
  | .refl => .refl
  | .tail head continuation =>
      .tail (.legacy head) (ofSteps continuation)

end GuardedSteps

/-
Guarded reduction is downward closed in its observation depth. The recursive
rule is the only nontrivial case: target depth zero is trivial, while a target
successor rebuilds the rule from a mutually lowered certificate.
-/
mutual
  theorem GuardedStep.lower
      (reduction : GuardedStep prior formation later context term result)
      (le : depth ≤ later) :
      GuardedStep prior formation depth context term result :=
    match reduction with
    | .zero => by
        have equality : depth = 0 := Nat.eq_zero_of_le_zero le
        subst depth
        exact .zero
    | .legacy reduction => .legacy reduction
    | .assumption membership => .assumption membership
    | .idempotent membership => .idempotent membership
    | .recursiveIdempotence defined certificate => by
        cases depth with
        | zero => exact .zero
        | succ depth =>
            exact .recursiveIdempotence defined
              (certificate.lower (Nat.succ_le_succ_iff.mp le))
    | .starChecking certificate => .starChecking (certificate.lower le)
    | .lam reduction => .lam (reduction.lower le)
    | .appLeft reduction => .appLeft (reduction.lower le)
    | .appRight reduction => .appRight (reduction.lower le)

  theorem GuardedSteps.lower
      (reduction : GuardedSteps prior formation later context term result)
      (le : depth ≤ later) :
      GuardedSteps prior formation depth context term result :=
    match reduction with
    | .refl => .refl
    | .tail head tail => .tail (head.lower le) (tail.lower le)
end

theorem GuardedStep.lowerSucc
    (reduction : GuardedStep prior formation (depth + 1) context term result) :
    GuardedStep prior formation depth context term result :=
  reduction.lower (Nat.le_succ depth)

theorem GuardedSteps.lowerSucc
    (reduction : GuardedSteps prior formation (depth + 1) context term result) :
    GuardedSteps prior formation depth context term result :=
  reduction.lower (Nat.le_succ depth)

namespace GuardedStep

/-- Guarded induction produces a directed recursive idempotence step. -/
theorem recursiveIdempotenceAt
    (defined : formation.defs name = some body)
    (guarded : ∀ depth, GuardedSteps prior formation depth
      (TypingContext.bind
        ((.app .star (.const name), .const name) ::
          (idempotenceLhs (.const name), idempotenceRhs (.const name)) ::
          context)
        (.const name))
      (.app (body.shift 1 0) (.app (.const name) (.bvar 0)))
      (.app (body.shift 1 0) (.bvar 0))) :
    ∀ depth, GuardedStep prior formation depth context
      (idempotenceLhs (.const name)) (idempotenceRhs (.const name))
  | 0 => .zero
  | depth + 1 => .recursiveIdempotence defined (guarded depth)

end GuardedStep

/-- Two terms with a common directed guarded reduct. -/
def GuardedJoinable (prior formation : DefEnv) (depth : Nat)
    (context : TypingContext) (left right : Term) : Prop :=
  ∃ join, GuardedSteps prior formation depth context left join ∧
    GuardedSteps prior formation depth context right join

namespace GuardedJoinable

theorem lower
    (joinable : GuardedJoinable prior formation later context left right)
    (le : depth ≤ later) :
    GuardedJoinable prior formation depth context left right := by
  obtain ⟨join, leftReduction, rightReduction⟩ := joinable
  exact ⟨join, leftReduction.lower le, rightReduction.lower le⟩

theorem lowerSucc
    (joinable : GuardedJoinable prior formation (depth + 1) context left right) :
    GuardedJoinable prior formation depth context left right :=
  joinable.lower (Nat.le_succ depth)

end GuardedJoinable

/-- Logical equality generated by guarded operational joinability. -/
inductive ContextEquiv (prior formation : DefEnv) :
    Nat → TypingContext → Term → Term → Prop where
  | operational : GuardedJoinable prior formation depth context left right →
      ContextEquiv prior formation depth context left right
  | refl : ContextEquiv prior formation depth context term term
  | symm : ContextEquiv prior formation depth context left right →
      ContextEquiv prior formation depth context right left
  | trans : ContextEquiv prior formation depth context left middle →
      ContextEquiv prior formation depth context middle right →
      ContextEquiv prior formation depth context left right
  | lam : ContextEquiv prior formation depth
      (context.map TypingContext.shiftEquation) body body' →
      ContextEquiv prior formation depth context (.lam body) (.lam body')
  | appLeft : ContextEquiv prior formation depth context function function' →
      ContextEquiv prior formation depth context
        (.app function argument) (.app function' argument)
  | appRight : ContextEquiv prior formation depth context argument argument' →
      ContextEquiv prior formation depth context
        (.app function argument) (.app function argument')
  | funext :
      ContextEquiv prior formation depth
        (context.map TypingContext.shiftEquation)
        (.app (left.shift 1 0) (.bvar 0))
        (.app (right.shift 1 0) (.bvar 0)) →
      ContextEquiv prior formation depth context left right

namespace ContextEquiv

/-- Guarded contextual equality is downward closed in observation depth. -/
theorem lower
    (equality : ContextEquiv prior formation later context left right)
    (le : depth ≤ later) :
    ContextEquiv prior formation depth context left right :=
  match equality with
  | .operational joinable => .operational (joinable.lower le)
  | .refl => .refl
  | .symm equality => .symm (equality.lower le)
  | .trans leftEquality rightEquality =>
      .trans (leftEquality.lower le) (rightEquality.lower le)
  | .lam equality => .lam (equality.lower le)
  | .appLeft equality => .appLeft (equality.lower le)
  | .appRight equality => .appRight (equality.lower le)
  | .funext equality => .funext (equality.lower le)

theorem lowerSucc
    (equality :
      ContextEquiv prior formation (depth + 1) context left right) :
    ContextEquiv prior formation depth context left right :=
  equality.lower (Nat.le_succ depth)

/-- A directed guarded reduction induces logical equality. -/
theorem ofGuardedSteps
    (reduction : GuardedSteps prior formation depth context left right) :
    ContextEquiv prior formation depth context left right :=
  .operational ⟨right, reduction, .refl⟩

/-- Every validated legacy step embeds into guarded logical equality. -/
theorem ofStep (reduction : Step prior stage left right) :
  ContextEquiv prior formation depth context left right :=
  ofGuardedSteps (.single (.legacy reduction))

theorem ofGuardedStep
    (reduction : GuardedStep prior formation depth context left right) :
    ContextEquiv prior formation depth context left right :=
  ofGuardedSteps (.single reduction)

/-- Directed idempotence checking yields the logical star equation. -/
theorem starChecking
    (certificate : GuardedSteps prior formation depth context
      (idempotenceLhs term) (idempotenceRhs term)) :
    ContextEquiv prior formation depth context (.app .star term) term :=
  ofGuardedStep (.starChecking certificate)

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
def assumptionStep (prior formation : DefEnv) (depth : Nat)
  (context : TypingContext) (term : Term) :
  Option { result // GuardedStep prior formation depth context term result } :=
  match lookupEquation context term with
  | none => none
  | some ⟨result, membership⟩ => some ⟨result, .assumption membership⟩

/--
One leftmost contextual contraction with a directed certificate. Every
non-legacy contraction comes from an explicit scoped equation.
-/
def contextualStep (prior formation : DefEnv) (depth : Nat)
    (context : TypingContext) :
    (term : Term) →
  Option { result // GuardedStep prior formation depth context term result }
  | .bvar index => assumptionStep prior formation depth context (.bvar index)
  | .const name => assumptionStep prior formation depth context (.const name)
  | .star => assumptionStep prior formation depth context .star
  | .lam body =>
    match assumptionStep prior formation depth context (.lam body) with
    | some step => some step
    | none =>
      match contextualStep prior formation depth
        (context.map TypingContext.shiftEquation) body with
      | none => none
      | some ⟨body', proof⟩ =>
        some ⟨.lam body', GuardedStep.lam (context := context) proof⟩
  | .app (.lam body) argument =>
    match assumptionStep prior formation depth context (.app (.lam body) argument) with
    | some step => some step
    | none =>
      match contextualStep prior formation depth context argument with
      | some ⟨argument', proof⟩ =>
        some ⟨.app (.lam body) argument', .appRight proof⟩
      | none => some ⟨body.instantiate argument, by
          have reduction : Step prior 0 (.app (.lam body) argument)
            (body.instantiate argument) := .beta
          exact .legacy reduction⟩
  | Term.app Term.star Term.star =>
    match assumptionStep prior formation depth context (.app .star .star) with
    | some step => some step
    | none => some ⟨.star, by
      obtain ⟨stage, reduction⟩ := star_star prior
      exact .legacy reduction⟩
  | Term.app Term.star (Term.app Term.star type) =>
    match assumptionStep prior formation depth context (.app .star (.app .star type)) with
    | some step => some step
    | none => some ⟨.app .star type, by
      obtain ⟨stage, reduction⟩ := star_starApp prior type
      exact .legacy reduction⟩
  | .app (.app .star type) (.app (.app .star type') argument) =>
    match assumptionStep prior formation depth context
      (.app (.app .star type) (.app (.app .star type') argument)) with
    | some step => some step
    | none =>
      if equality : type = type' then
      some ⟨.app (.app .star type) argument, by
        subst type'
        have reduction : Step prior 0
            (.app (.app .star type) (.app (.app .star type) argument))
            (.app (.app .star type) argument) := .starredIdempotence
        exact .legacy reduction⟩
      else
      match contextualStep prior formation depth context (.app .star type) with
      | some ⟨function', proof⟩ =>
        some ⟨.app function' (.app (.app .star type') argument),
          .appLeft proof⟩
      | none =>
        match contextualStep prior formation depth context
          (.app (.app .star type') argument) with
        | none => none
        | some ⟨argument', proof⟩ =>
          some ⟨.app (.app .star type) argument', .appRight proof⟩
  | .app type (.app type' argument) =>
    match assumptionStep prior formation depth context (.app type (.app type' argument)) with
    | some step => some step
    | none =>
      if equality : type = type' then
      if membership : (.app .star type, type) ∈ context then
        some ⟨.app type argument, by
        subst type'
        exact .idempotent membership⟩
      else
        match contextualStep prior formation depth context type with
        | some ⟨type'', proof⟩ =>
          some ⟨.app type'' (.app type' argument), .appLeft proof⟩
        | none =>
          match contextualStep prior formation depth context (.app type' argument) with
          | none => none
          | some ⟨argument', proof⟩ =>
            some ⟨.app type argument', .appRight proof⟩
      else
      match contextualStep prior formation depth context type with
      | some ⟨type'', proof⟩ =>
        some ⟨.app type'' (.app type' argument), .appLeft proof⟩
      | none =>
        match contextualStep prior formation depth context (.app type' argument) with
        | none => none
        | some ⟨argument', proof⟩ =>
          some ⟨.app type argument', .appRight proof⟩
  | .app function argument =>
    match assumptionStep prior formation depth context (.app function argument) with
    | some step => some step
    | none =>
      match contextualStep prior formation depth context function with
      | some ⟨function', proof⟩ =>
        some ⟨.app function' argument, .appLeft proof⟩
      | none =>
        match contextualStep prior formation depth context argument with
        | none => none
        | some ⟨argument', proof⟩ =>
          some ⟨.app function argument', .appRight proof⟩

/-- Fuel-bounded contextual normalization with a directed certificate. -/
def contextualSteps (prior formation : DefEnv) (depth : Nat)
    (context : TypingContext) :
    (fuel : Nat) → (term : Term) →
      { result // GuardedSteps prior formation depth context term result }
  | 0, term => ⟨term, .refl⟩
  | fuel + 1, term =>
      match contextualStep prior formation depth context term with
      | none => ⟨term, .refl⟩
      | some ⟨middle, head⟩ =>
          let tail := contextualSteps prior formation depth context fuel middle
          ⟨tail.1, .tail head tail.2⟩

/-- Fuel-bounded contextual reduction that stops upon reaching its target. -/
def contextualStepsUntil (prior formation : DefEnv) (depth : Nat)
    (context : TypingContext) :
    (fuel : Nat) → (term target : Term) →
      { result // GuardedSteps prior formation depth context term result }
  | 0, term, _ => ⟨term, .refl⟩
  | fuel + 1, term, target =>
      if equality : term = target then
        ⟨target, by subst target; exact .refl⟩
      else
        match contextualStep prior formation depth context term with
        | none => ⟨term, .refl⟩
        | some ⟨middle, head⟩ =>
            let tail := contextualStepsUntil prior formation depth context
              fuel middle target
            ⟨tail.1, .tail head tail.2⟩

/-- Reaching a requested target supplies its directed reduction certificate. -/
theorem contextualStepsTo (depth fuel : Nat)
    (equality :
      (contextualStepsUntil prior formation depth context fuel term target).1 =
        target) :
    GuardedSteps prior formation depth context term target := by
  let reduction := contextualStepsUntil prior formation depth context
    fuel term target
  rw [← equality]
  exact reduction.2

/-- Equal computed contextual normal forms give a contextual equality. -/
theorem ofContextualStepsEq (depth fuel : Nat)
    (equality :
      (contextualSteps prior formation depth context fuel right).1 =
        (contextualSteps prior formation depth context fuel left).1) :
    ContextEquiv prior formation depth context left right := by
  let leftReduction := contextualSteps prior formation depth context fuel left
  let rightReduction := contextualSteps prior formation depth context fuel right
  apply ContextEquiv.operational
  exact ⟨leftReduction.1, leftReduction.2, by
    change rightReduction.1 = leftReduction.1 at equality
    rw [← equality]
    exact rightReduction.2⟩

end ContextEquiv

/-- `Checks Γ t A` requires projector equality at every observation depth. -/
inductive Checks (prior formation : DefEnv) :
    TypingContext → Term → Term → Prop where
  | certified
      (certificate : ∀ depth, ContextEquiv prior formation depth context
        (.app type term) term) :
      Checks prior formation context term type
  | conversion
      (premise : Checks prior formation context term sourceType)
      (equality : ∀ depth, ContextEquiv prior formation depth context
        sourceType targetType) :
      Checks prior formation context term targetType

/-- Every self-typing derivation denotes projector equality. -/
theorem Checks.sound : Checks prior formation context term type →
  ∀ depth, ContextEquiv prior formation depth context (.app type term) term
  | .certified certificate => certificate
  | @Checks.conversion _ _ context term sourceType targetType premise equality => by
      intro depth
      exact .trans (.appLeft (.symm (equality depth))) (premise.sound depth)

end LambdaStar
