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
      Nat → Nat → TypingContext → Term → Term → Prop where
    | zero : GuardedStep prior formation 0 0 context left right
    | later : GuardedStep prior formation (depth + 1) depth context term term
    | legacy (reduction : Step DefEnv.empty stage left right) :
        GuardedStep prior formation depth depth context left right
    | delta (defined : prior.defs name = some body) :
        GuardedStep prior formation (depth + 1) depth context
          (.app (.const name) argument) (.app body argument)
    | assumption (membership : (left, right) ∈ context) :
        GuardedStep prior formation depth depth context left right
    | idempotent
        (membership : (.app .star type, type) ∈ context) :
        GuardedStep prior formation depth depth context
          (.app type (.app type term)) (.app type term)
    | recursiveIdempotence
        (defined : formation.defs name = some body)
        (certificate : GuardedSteps prior formation sourceDepth remainingDepth
          (TypingContext.bind
            ((.app .star (.const name), .const name) ::
              (idempotenceLhs (.const name), idempotenceRhs (.const name)) ::
              context)
            (.const name))
          (.app (body.shift 1 0) (.app (.const name) (.bvar 0)))
          (.app (body.shift 1 0) (.bvar 0))) :
        GuardedStep prior formation (sourceDepth + 1) (remainingDepth + 1) context
          (idempotenceLhs (.const name)) (idempotenceRhs (.const name))
    | starChecking
        (certificate : GuardedSteps prior formation sourceDepth remainingDepth context
          (idempotenceLhs term) (idempotenceRhs term)) :
        GuardedStep prior formation sourceDepth remainingDepth context
          (.app .star term) term
    | lam : GuardedStep prior formation sourceDepth remainingDepth
        (context.map TypingContext.shiftEquation) body body' →
        GuardedStep prior formation sourceDepth remainingDepth context
          (.lam body) (.lam body')
    | appLeft : GuardedStep prior formation sourceDepth remainingDepth context
        function function' →
        GuardedStep prior formation sourceDepth remainingDepth context
          (.app function argument) (.app function' argument)
    | appRight : GuardedStep prior formation sourceDepth remainingDepth context
        argument argument' →
        GuardedStep prior formation sourceDepth remainingDepth context
          (.app function argument) (.app function argument')

  /-- Reflexive-transitive guarded reduction, threading observation depth. -/
  inductive GuardedSteps (prior formation : DefEnv) :
      Nat → Nat → TypingContext → Term → Term → Prop where
    | refl : GuardedSteps prior formation depth depth context term term
    | tail : GuardedStep prior formation sourceDepth middleDepth context term middle →
        GuardedSteps prior formation middleDepth remainingDepth context middle result →
        GuardedSteps prior formation sourceDepth remainingDepth context term result
end

namespace GuardedSteps

theorem single
    (step : GuardedStep prior formation sourceDepth remainingDepth context term result) :
    GuardedSteps prior formation sourceDepth remainingDepth context term result :=
  .tail step .refl

theorem trans :
    GuardedSteps prior formation sourceDepth middleDepth context left middle →
    GuardedSteps prior formation middleDepth remainingDepth context middle right →
    GuardedSteps prior formation sourceDepth remainingDepth context left right
  | .refl, continuation => continuation
  | .tail head continuation, rest =>
      .tail head (trans continuation rest)

/-- Forget a finite amount of observation depth without changing the term. -/
theorem spend (cost baseDepth : Nat) :
    GuardedSteps prior formation (cost + baseDepth) baseDepth context term term := by
  induction cost with
  | zero => simpa using (GuardedSteps.refl :
      GuardedSteps prior formation baseDepth baseDepth context term term)
  | succ cost inductionHypothesis =>
      rw [Nat.succ_add]
      exact .tail .later inductionHypothesis

/-- Embed environment-free staged reduction without changing its stage. -/
theorem ofSteps : Steps DefEnv.empty stage left right →
  GuardedSteps prior formation depth depth context left right
  | .refl => .refl
  | .tail head continuation =>
      .tail (.legacy head) (ofSteps continuation)

end GuardedSteps

namespace GuardedStep

/-- Guarded induction produces a directed recursive idempotence step. -/
theorem recursiveIdempotenceAt
    (defined : formation.defs name = some body)
    (guarded : GuardedSteps prior formation sourceDepth remainingDepth
      (TypingContext.bind
        ((.app .star (.const name), .const name) ::
          (idempotenceLhs (.const name), idempotenceRhs (.const name)) ::
          context)
        (.const name))
      (.app (body.shift 1 0) (.app (.const name) (.bvar 0)))
      (.app (body.shift 1 0) (.bvar 0))) :
    GuardedStep prior formation (sourceDepth + 1) (remainingDepth + 1) context
      (idempotenceLhs (.const name)) (idempotenceRhs (.const name)) :=
  .recursiveIdempotence defined guarded

end GuardedStep

/-- Two terms with a common directed guarded reduct. -/
def GuardedJoinable (prior formation : DefEnv) (depth : Nat)
    (context : TypingContext) (left right : Term) : Prop :=
  ∃ remainingDepth join,
    GuardedSteps prior formation depth remainingDepth context left join ∧
    GuardedSteps prior formation depth remainingDepth context right join

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

/-- At observation depth zero, both terms reduce to any chosen common term. -/
theorem zero : ContextEquiv prior formation 0 context left right :=
  .operational ⟨0, right, .single .zero, .refl⟩

/-- A directed guarded reduction induces logical equality. -/
theorem ofGuardedSteps
    (reduction : GuardedSteps prior formation depth depth
      context left right) :
    ContextEquiv prior formation depth context left right :=
  .operational ⟨depth, right, reduction, .refl⟩

/-- Every environment-free staged step embeds into guarded logical equality. -/
theorem ofStep (reduction : Step DefEnv.empty stage left right) :
  ContextEquiv prior formation depth context left right :=
  ofGuardedSteps (.single (.legacy reduction))

theorem ofGuardedStep
    (reduction : GuardedStep prior formation depth depth
      context left right) :
    ContextEquiv prior formation depth context left right :=
  ofGuardedSteps (.single reduction)

/-- Directed idempotence checking yields the logical star equation. -/
theorem starChecking
    (certificate : GuardedSteps prior formation depth depth context
      (idempotenceLhs term) (idempotenceRhs term)) :
    ContextEquiv prior formation depth context (.app .star term) term :=
  ofGuardedStep (.starChecking certificate)

abbrev GuardedStepResult (prior formation : DefEnv) (sourceDepth : Nat)
    (context : TypingContext) (term : Term) :=
  Σ remainingDepth, { result //
    GuardedStep prior formation sourceDepth remainingDepth context term result }

abbrev GuardedStepsResult (prior formation : DefEnv) (sourceDepth : Nat)
    (context : TypingContext) (term : Term) :=
  Σ remainingDepth, { result //
    GuardedSteps prior formation sourceDepth remainingDepth context term result }

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
  Option (GuardedStepResult prior formation depth context term) :=
  match lookupEquation context term with
  | none => none
  | some ⟨result, membership⟩ =>
      some ⟨depth, result, .assumption membership⟩

/-- Unfold a validated prior definition, consuming one observation depth. -/
def priorDeltaStep (prior formation : DefEnv) (depth : Nat)
    (context : TypingContext) (allowDelta : Bool)
    (function argument : Term) :
    Option (GuardedStepResult prior formation depth context
      (.app function argument)) :=
  if allowDelta then
    match depth, function with
    | remainingDepth + 1, .const name =>
      match defined : prior.defs name with
      | some body => some ⟨remainingDepth, .app body argument, .delta defined⟩
      | none => none
    | _, _ => none
  else none

/--
One leftmost contextual contraction with a directed certificate. Every
non-legacy contraction comes from an explicit scoped equation.
-/
def contextualStep (prior formation : DefEnv) (depth : Nat)
  (context : TypingContext) (allowDelta : Bool := true) :
    (term : Term) →
  Option (GuardedStepResult prior formation depth context term)
  | .bvar index => assumptionStep prior formation depth context (.bvar index)
  | .const name => assumptionStep prior formation depth context (.const name)
  | .star => assumptionStep prior formation depth context .star
  | .lam body =>
    match assumptionStep prior formation depth context (.lam body) with
    | some step => some step
    | none =>
      match contextualStep prior formation depth
        (context.map TypingContext.shiftEquation) (allowDelta := allowDelta) body with
      | none => none
      | some ⟨remainingDepth, body', proof⟩ =>
        some ⟨remainingDepth, .lam body',
          GuardedStep.lam (context := context) proof⟩
  | .app (.lam body) argument =>
    match assumptionStep prior formation depth context (.app (.lam body) argument) with
    | some step => some step
    | none =>
      match contextualStep prior formation depth context
        (allowDelta := allowDelta) argument with
      | some ⟨remainingDepth, argument', proof⟩ =>
        some ⟨remainingDepth, .app (.lam body) argument', .appRight proof⟩
      | none => some ⟨depth, body.instantiate argument, by
          have reduction : Step DefEnv.empty 0 (.app (.lam body) argument)
            (body.instantiate argument) := .beta
          exact .legacy reduction⟩
  | Term.app Term.star Term.star =>
    match assumptionStep prior formation depth context (.app .star .star) with
    | some step => some step
    | none => some ⟨depth, .star, by
      obtain ⟨stage, reduction⟩ := star_star DefEnv.empty
      exact .legacy reduction⟩
  | Term.app Term.star (Term.app Term.star type) =>
    match assumptionStep prior formation depth context (.app .star (.app .star type)) with
    | some step => some step
    | none => some ⟨depth, .app .star type, by
      obtain ⟨stage, reduction⟩ := star_starApp DefEnv.empty type
      exact .legacy reduction⟩
  | .app (.app .star type) (.app (.app .star type') argument) =>
    match assumptionStep prior formation depth context
      (.app (.app .star type) (.app (.app .star type') argument)) with
    | some step => some step
    | none =>
      if equality : type = type' then
      some ⟨depth, .app (.app .star type) argument, by
        subst type'
        have reduction : Step DefEnv.empty 0
            (.app (.app .star type) (.app (.app .star type) argument))
            (.app (.app .star type) argument) := .starredIdempotence
        exact .legacy reduction⟩
      else
      match contextualStep prior formation depth context
        (allowDelta := allowDelta) (.app .star type) with
      | some ⟨remainingDepth, function', proof⟩ =>
        some ⟨remainingDepth,
          .app function' (.app (.app .star type') argument),
          .appLeft proof⟩
      | none =>
        match contextualStep prior formation depth context (allowDelta := allowDelta)
          (.app (.app .star type') argument) with
        | none => none
        | some ⟨remainingDepth, argument', proof⟩ =>
          some ⟨remainingDepth, .app (.app .star type) argument',
            .appRight proof⟩
  | .app type (.app type' argument) =>
    match assumptionStep prior formation depth context (.app type (.app type' argument)) with
    | some step => some step
    | none =>
      if equality : type = type' then
      if membership : (.app .star type, type) ∈ context then
        some ⟨depth, .app type argument, by
        subst type'
        exact .idempotent membership⟩
      else
        match contextualStep prior formation depth context (allowDelta := allowDelta)
          type with
        | some ⟨remainingDepth, type'', proof⟩ =>
          some ⟨remainingDepth, .app type'' (.app type' argument), .appLeft proof⟩
        | none =>
          match contextualStep prior formation depth context (allowDelta := allowDelta)
            (.app type' argument) with
          | none => priorDeltaStep prior formation depth context allowDelta
              type (.app type' argument)
          | some ⟨remainingDepth, argument', proof⟩ =>
            some ⟨remainingDepth, .app type argument', .appRight proof⟩
      else
      match contextualStep prior formation depth context (allowDelta := allowDelta)
        type with
      | some ⟨remainingDepth, type'', proof⟩ =>
        some ⟨remainingDepth, .app type'' (.app type' argument), .appLeft proof⟩
      | none =>
        match contextualStep prior formation depth context (allowDelta := allowDelta)
          (.app type' argument) with
        | none => priorDeltaStep prior formation depth context allowDelta
            type (.app type' argument)
        | some ⟨remainingDepth, argument', proof⟩ =>
          some ⟨remainingDepth, .app type argument', .appRight proof⟩
  | .app function argument =>
    match assumptionStep prior formation depth context (.app function argument) with
    | some step => some step
    | none =>
      match contextualStep prior formation depth context (allowDelta := allowDelta)
        function with
      | some ⟨remainingDepth, function', proof⟩ =>
        some ⟨remainingDepth, .app function' argument, .appLeft proof⟩
      | none =>
        match contextualStep prior formation depth context (allowDelta := allowDelta)
          argument with
        | none => priorDeltaStep prior formation depth context allowDelta
            function argument
        | some ⟨remainingDepth, argument', proof⟩ =>
          some ⟨remainingDepth, .app function argument', .appRight proof⟩

/-- Fuel-bounded contextual normalization with a directed certificate. -/
def contextualSteps (prior formation : DefEnv) (depth : Nat)
  (context : TypingContext) (allowDelta : Bool := true) :
    (fuel : Nat) → (term : Term) →
    GuardedStepsResult prior formation depth context term
  | 0, term => ⟨depth, term, .refl⟩
  | fuel + 1, term =>
      match contextualStep prior formation depth context (allowDelta := allowDelta)
        term with
    | none => ⟨depth, term, .refl⟩
    | some ⟨middleDepth, middle, head⟩ =>
          let tail := contextualSteps prior formation middleDepth context
            (allowDelta := allowDelta) fuel middle
      ⟨tail.1, tail.2.1, .tail head tail.2.2⟩

/-- Fuel-bounded contextual reduction that stops upon reaching its target. -/
def contextualStepsUntil (prior formation : DefEnv) (depth : Nat)
  (context : TypingContext) (allowDelta : Bool := true) :
    (fuel : Nat) → (term target : Term) →
      GuardedStepsResult prior formation depth context term
  | 0, term, target =>
      match depth with
      | 0 => ⟨0, target, .single .zero⟩
      | depth + 1 => ⟨depth + 1, term, .refl⟩
  | fuel + 1, term, target =>
      if equality : term = target then
        ⟨depth, target, by subst target; exact .refl⟩
      else
        match depth with
        | 0 => ⟨0, target, .single .zero⟩
        | depth + 1 =>
          match contextualStep prior formation (depth + 1) context
            (allowDelta := allowDelta) term with
          | none => ⟨depth + 1, term, .refl⟩
          | some ⟨middleDepth, middle, head⟩ =>
            let tail := contextualStepsUntil prior formation middleDepth context
              (allowDelta := allowDelta) fuel middle target
            ⟨tail.1, tail.2.1, .tail head tail.2.2⟩

/-- Reaching a requested depth and target supplies its directed certificate. -/
theorem contextualStepsTo (depth remainingDepth fuel : Nat)
    (allowDelta : Bool := true)
    (depthEquality :
      (contextualStepsUntil prior formation depth context
        (allowDelta := allowDelta) fuel term target).1 =
        remainingDepth)
    (equality :
      (contextualStepsUntil prior formation depth context
        (allowDelta := allowDelta) fuel term target).2.1 =
        target) :
    GuardedSteps prior formation depth remainingDepth context term target := by
  let reduction := contextualStepsUntil prior formation depth context
    (allowDelta := allowDelta) fuel term target
  have atRemainingDepth : GuardedSteps prior formation depth remainingDepth
      context term reduction.2.1 :=
    Eq.mp
      (congrArg
        (fun resultDepth => GuardedSteps prior formation depth resultDepth
          context term reduction.2.1)
        depthEquality)
      reduction.2.2
  exact Eq.mp
    (congrArg
      (fun result => GuardedSteps prior formation depth remainingDepth
        context term result)
      equality)
    atRemainingDepth

/-- Equal computed contextual normal forms give a contextual equality. -/
theorem ofContextualStepsEqWithStrategy (depth fuel : Nat) (allowDelta : Bool)
    (equality :
      ((contextualSteps prior formation depth context (allowDelta := allowDelta)
          fuel right).1,
        (contextualSteps prior formation depth context (allowDelta := allowDelta)
          fuel right).2.1) =
      ((contextualSteps prior formation depth context (allowDelta := allowDelta)
          fuel left).1,
        (contextualSteps prior formation depth context (allowDelta := allowDelta)
          fuel left).2.1)) :
    ContextEquiv prior formation depth context left right := by
  let leftReduction := contextualSteps prior formation depth context
    (allowDelta := allowDelta) fuel left
  let rightReduction := contextualSteps prior formation depth context
    (allowDelta := allowDelta) fuel right
  have depthEquality : rightReduction.1 = leftReduction.1 :=
    congrArg Prod.fst equality
  have termEquality : rightReduction.2.1 = leftReduction.2.1 :=
    congrArg Prod.snd equality
  have rightAtCommonDepth : GuardedSteps prior formation depth leftReduction.1
      context right rightReduction.2.1 :=
    depthEquality ▸ rightReduction.2.2
  apply ContextEquiv.operational
  exact ⟨leftReduction.1, leftReduction.2.1, leftReduction.2.2, by
    rw [← termEquality]
    exact rightAtCommonDepth⟩

theorem ofContextualStepsEq (depth fuel : Nat)
    (equality :
      ((contextualSteps prior formation depth context (allowDelta := true)
          fuel right).1,
        (contextualSteps prior formation depth context (allowDelta := true)
          fuel right).2.1) =
      ((contextualSteps prior formation depth context (allowDelta := true)
          fuel left).1,
        (contextualSteps prior formation depth context (allowDelta := true)
          fuel left).2.1)) :
    ContextEquiv prior formation depth context left right :=
  ofContextualStepsEqWithStrategy depth fuel true equality

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
