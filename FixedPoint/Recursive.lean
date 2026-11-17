import FixedPoint.Examples

namespace FixedPoint

theorem Environment.eq_of_definitions
  (left right : Environment)
  (sameDefinitions : left.definitions = right.definitions) : left = right := by
  cases left
  cases right
  cases sameDefinitions
  rfl

/-- Extend an environment with one fresh definition for recursive type formation. -/
def Environment.extendOne (prior : Environment) (definition : RecursiveDefinition)
    (fresh : prior.lookup definition.name = none) : Environment where
  definitions := prior.definitions ++ [definition]
  namesUnique := by
    simp only [List.map_append, List.map_singleton]
    rw [List.nodup_append]
    refine ⟨prior.namesUnique, by simp, ?_⟩
    intro name inPrior currentName inCurrent
    simp only [List.mem_singleton] at inCurrent
    subst currentName
    intro namesEqual
    subst name
    obtain ⟨priorDefinition, priorMembership, sameName⟩ := List.mem_map.mp inPrior
    have noMatch : ∀ candidate ∈ prior.definitions,
        ¬candidate.name = definition.name := by
      simpa [Environment.lookup] using fresh
    exact noMatch priorDefinition priorMembership sameName

/-- A body realizes its annotation under the phase-appropriate environments. -/
inductive ChecksImplementation
    (prior formation : Environment) (name : Const) : Term → Term → Prop where
  | direct (check : Membership prior [] body annotation) :
      ChecksImplementation prior formation name body annotation
  | recursiveTypeFormation
      (defined : formation.lookupBody name = some body)
      (check : Membership formation [] body Examples.typeTerm) :
      ChecksImplementation prior formation name body Examples.typeTerm
  | namedProjector
      (defined : prior.lookupBody annotationName = some (.lam .any projectorBody))
      (check : Convertible formation []
        (projectorBody.instantiate (.const name)) body) :
      ChecksImplementation prior formation name body (.const annotationName)

/--
One phase checked against earlier definitions. Each body receives a singleton
formation environment, permitting guarded self-unfolding but never sibling
unfolding.
-/
structure RecursivePhaseValidation (prior : Environment) where
  definitions : List RecursiveDefinition
  namesUnique : (definitions.map (·.name)).Nodup
  fresh : ∀ definition ∈ definitions, prior.lookup definition.name = none
  combinedNamesUnique :
    ((prior.definitions ++ definitions).map (·.name)).Nodup
  bodiesChecked : ∀ (definition) (membership : definition ∈ definitions),
    ChecksImplementation
      prior
      (prior.extendOne definition (fresh definition membership))
      definition.name definition.body definition.annotation

namespace RecursivePhaseValidation

def environment (phase : RecursivePhaseValidation prior) : Environment where
  definitions := prior.definitions ++ phase.definitions
  namesUnique := phase.combinedNamesUnique

end RecursivePhaseValidation

/-- A phase-by-phase proof that every supplied definition is validated exactly once. -/
inductive ValidationHistory :
    List RecursiveDefinition → Environment → Environment → Prop where
  | nil (environment) : ValidationHistory [] environment environment
  | cons
      (phase : RecursivePhaseValidation prior)
      (rest : ValidationHistory remaining phase.environment result) :
      ValidationHistory (phase.definitions ++ remaining) prior result

/-- An environment sealed by complete validation of its supplied definitions. -/
structure ValidatedEnv (supplied : List RecursiveDefinition) where
  environment : Environment
  validation : ValidationHistory supplied .empty environment

/-- A validated recursive name inhabits its signature by recursive induction. -/
theorem recursive_induction
    (validated : ValidatedEnv supplied)
    (declared : validated.environment.lookupAnnotation name = some annotation) :
    Membership validated.environment context (.const name) annotation :=
  ⟨0, .step (.recursiveInduction declared)⟩

/-- Applying a recursive name exposes its body; a bare name remains stable. -/
theorem unfold_applied
    (validated : ValidatedEnv supplied)
    (defined : validated.environment.lookupBody name = some body) :
    ReducesOne validated.environment context (.app (.const name) argument)
      (.app body argument) :=
  ⟨0, .delta defined⟩

/-- No reduction rule unfolds or changes an unapplied recursive name. -/
theorem Step.no_const_source
    (reduction : Step environment stage context (.const name) result) : False :=
  match reduction with
  | .lift reduction => reduction.no_const_source

theorem Steps.const_source
    (reduction : Steps environment stage context (.const name) result) :
    result = .const name := by
  cases reduction with
  | refl => rfl
  | tail head _ => exact False.elim head.no_const_source

end FixedPoint
