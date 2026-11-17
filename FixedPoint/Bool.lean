import FixedPoint.Examples
import FixedPoint.Recursive

namespace FixedPoint.Bool

open FixedPoint Term
open FixedPoint.Examples (typeTerm)

set_option maxRecDepth 10000

abbrev boolName : Const := "Bool"
abbrev trueName : Const := "true"
abbrev falseName : Const := "false"

/-- `A → B = λf : Any. λx : A. B (f (A x))`. -/
def arrowTerm (domain codomain : Term) : Term :=
  .lam .any
    (.lam (domain.shift 1)
      (.app (codomain.shift 2)
        (.app (.bvar 1) (.app (domain.shift 2) (.bvar 0)))))

/-- `Bool → Type`. -/
def predicateType : Term := arrowTerm (.const boolName) typeTerm

/--
`λb : Any. λP : Bool → Type. λt : P true. λf : P false.
  (P b) (b P t f)`.
-/
def boolBody : Term :=
  .lam .any
    (.lam predicateType
      (.lam (.app (.bvar 0) (.const trueName))
        (.lam (.app (.bvar 1) (.const falseName))
          (.app (.app (.bvar 2) (.bvar 3))
            (.app (.app (.app (.bvar 3) (.bvar 2)) (.bvar 1)) (.bvar 0))))))

/-- `λP : Bool → Type. λt : P true. λf : P false. t`. -/
def trueBody : Term :=
  .lam predicateType
    (.lam (.app (.bvar 0) (.const trueName))
      (.lam (.app (.bvar 1) (.const falseName)) (.bvar 1)))

/-- `λP : Bool → Type. λt : P true. λf : P false. f`. -/
def falseBody : Term :=
  .lam predicateType
    (.lam (.app (.bvar 0) (.const trueName))
      (.lam (.app (.bvar 1) (.const falseName)) (.bvar 0)))

private theorem boolBody_closed : boolBody.Closed := by decide
private theorem trueBody_closed : trueBody.Closed := by decide
private theorem falseBody_closed : falseBody.Closed := by decide

def boolDefinition : RecursiveDefinition :=
  ⟨boolName, typeTerm, boolBody, by decide, boolBody_closed⟩

def trueDefinition : RecursiveDefinition :=
  ⟨trueName, .const boolName, trueBody, by decide, trueBody_closed⟩

def falseDefinition : RecursiveDefinition :=
  ⟨falseName, .const boolName, falseBody, by decide, falseBody_closed⟩

/-- The Bool projector is validated before either constructor is exposed. -/
def boolPhaseDefinitions : List RecursiveDefinition :=
  [boolDefinition]

/-- The constructors share a phase but are checked without seeing each other. -/
def constructorPhaseDefinitions : List RecursiveDefinition :=
  [trueDefinition, falseDefinition]

def definitions : List RecursiveDefinition :=
  boolPhaseDefinitions ++ constructorPhaseDefinitions

def boolPhaseEnvironment : Environment where
  definitions := boolPhaseDefinitions
  namesUnique := by decide

def provisionalFormation : Environment :=
  Environment.empty.extendOne boolDefinition (by rfl)

def boolEnvironment : Environment where
  definitions := definitions
  namesUnique := by decide

abbrev BoolBodyCheck : Prop :=
  ChecksImplementation Environment.empty
    provisionalFormation
    boolName boolBody typeTerm

abbrev TrueBodyCheck : Prop :=
  ChecksImplementation boolPhaseEnvironment
    (boolPhaseEnvironment.extendOne trueDefinition (by rfl))
    trueName trueBody (.const boolName)

abbrev FalseBodyCheck : Prop :=
  ChecksImplementation boolPhaseEnvironment
    (boolPhaseEnvironment.extendOne falseDefinition (by rfl))
    falseName falseBody (.const boolName)

private theorem stableBool_idempotent (context : Context) :
    Equiv provisionalFormation 1 context
      (.lam .any
        (.app (.const boolName) (.app (.const boolName) (.bvar 0))))
      (.lam .any (.app (.const boolName) (.bvar 0))) := by
  apply Equiv.trans (middle := .app typeTerm (.const boolName))
  · exact .symm (.step (.beta (.step .any)))
  · apply Equiv.trans (middle := .const boolName)
    · exact .step (.lift (.recursiveInduction (by rfl)))
    · exact .symm (by
        simpa [Term.shift] using
          (Equiv.etaAny (environment := provisionalFormation) (stage := 1)
            (context := context) (term := .const boolName)))

private theorem stableBool_idempotent_at_variable :
    Equiv provisionalFormation 1 [.any]
      (.app (.const boolName) (.app (.const boolName) (.bvar 0)))
      (.app (.const boolName) (.bvar 0)) := by
  apply Equiv.trans (middle :=
    .app
      (.lam .any
        (.app (.const boolName) (.app (.const boolName) (.bvar 0))))
      (.bvar 0))
  · exact .symm (.step (.beta (.step (.assumption (by rfl)))))
  · apply Equiv.trans (middle :=
      .app (.lam .any (.app (.const boolName) (.bvar 0))) (.bvar 0))
    · exact .app (stableBool_idempotent [.any]) .refl
    · exact .step (.beta (.step (.assumption (by rfl))))

private theorem boolBody_idempotent_at_variable :
    Equiv provisionalFormation 1 [.any]
      (.app boolBody (.app boolBody (.bvar 0)))
      (.app boolBody (.bvar 0)) := by
  apply Equiv.trans (middle :=
    .app (.const boolName) (.app (.const boolName) (.bvar 0)))
  · apply Equiv.symm
    apply Equiv.trans (middle :=
      .app (.const boolName) (.app boolBody (.bvar 0)))
    · exact .step (.appRight (.lift (.delta (by rfl))))
    · exact .step (.lift (.delta (by rfl)))
  · apply Equiv.trans (middle := .app (.const boolName) (.bvar 0))
    · exact stableBool_idempotent_at_variable
    · exact .step (.lift (.delta (by rfl)))

theorem bool_has_type :
    Membership provisionalFormation [] boolBody typeTerm := by
  refine ⟨1, ?_⟩
  apply Equiv.trans (middle :=
    .lam .any (.app boolBody (.app boolBody (.bvar 0))))
  · exact .step (.beta (.step .any))
  · apply Equiv.trans (middle := .lam .any (.app boolBody (.bvar 0)))
    · exact .lamBody boolBody_idempotent_at_variable
    · simpa [boolBody, predicateType, arrowTerm, typeTerm, Term.shift] using
        (Equiv.etaAny (environment := provisionalFormation) (stage := 1)
          (context := []) (term := boolBody))

theorem bool_implementation_check : BoolBodyCheck := by
  exact .recursiveTypeFormation (by rfl) bool_has_type

private theorem true_family_converts :
  Convertible (boolPhaseEnvironment.extendOne trueDefinition (by rfl)) []
      (.lam predicateType
        (.lam (.app (.bvar 0) (.const trueName))
          (.lam (.app (.bvar 1) (.const falseName))
            (.app (.app (.bvar 2) (.const trueName))
              (.app (.app (.app (.const trueName) (.bvar 2)) (.bvar 1))
                (.bvar 0))))))
      trueBody := by
  refine ⟨1, ?_⟩
  apply Equiv.lamBody
  apply Equiv.lamBody
  apply Equiv.lamBody
  apply Equiv.trans
  · apply Equiv.app
    · exact .refl
    · apply Equiv.trans
      · exact .step (.appLeft (.appLeft (.lift (.delta (by rfl)))))
      · apply Equiv.trans
        · exact .step (.appLeft (.appLeft (.beta (.step (.assumption (by
            simp [Context.Lookup, Context.extend, predicateType,
              arrowTerm, typeTerm, Term.shift]))))))
        · apply Equiv.trans
          · exact .step (.appLeft (.beta (.step (.assumption (by
              simp [Context.Lookup, Context.extend, predicateType,
                arrowTerm, Term.shift, Term.substAt])))))
          · exact .step (.beta (.step (.assumption (by
              simp [Context.Lookup, Context.extend, predicateType,
                arrowTerm, Term.shift, Term.substAt]))))
  · exact .step (.assumption (by
      simp [Context.Lookup, Context.extend, predicateType, arrowTerm,
        Term.shift]))

theorem true_has_type : TrueBodyCheck := by
  apply ChecksImplementation.namedProjector
  · rfl
  · simpa [boolBody, predicateType, arrowTerm, typeTerm, Term.instantiate,
      Term.substAt, Term.shift] using true_family_converts

private theorem false_family_converts :
  Convertible (boolPhaseEnvironment.extendOne falseDefinition (by rfl)) []
      (.lam predicateType
        (.lam (.app (.bvar 0) (.const trueName))
          (.lam (.app (.bvar 1) (.const falseName))
            (.app (.app (.bvar 2) (.const falseName))
              (.app (.app (.app (.const falseName) (.bvar 2)) (.bvar 1))
                (.bvar 0))))))
      falseBody := by
  refine ⟨1, ?_⟩
  apply Equiv.lamBody
  apply Equiv.lamBody
  apply Equiv.lamBody
  apply Equiv.trans
  · apply Equiv.app
    · exact .refl
    · apply Equiv.trans
      · exact .step (.appLeft (.appLeft (.lift (.delta (by rfl)))))
      · apply Equiv.trans
        · exact .step (.appLeft (.appLeft (.beta (.step (.assumption (by
            simp [Context.Lookup, Context.extend, predicateType,
              arrowTerm, typeTerm, Term.shift]))))))
        · apply Equiv.trans
          · exact .step (.appLeft (.beta (.step (.assumption (by
              simp [Context.Lookup, Context.extend, predicateType,
                arrowTerm, Term.shift, Term.substAt])))))
          · exact .step (.beta (.step (.assumption (by
              simp [Context.Lookup, Context.extend, predicateType,
                arrowTerm, Term.shift, Term.substAt]))))
  · exact .step (.assumption (by
      simp [Context.Lookup, Context.extend, predicateType, arrowTerm,
        Term.shift]))

theorem false_has_type : FalseBodyCheck := by
  apply ChecksImplementation.namedProjector
  · rfl
  · simpa [boolBody, predicateType, arrowTerm, typeTerm, Term.instantiate,
      Term.substAt, Term.shift] using false_family_converts

def boolPhaseValidation : RecursivePhaseValidation Environment.empty :=
  { definitions := boolPhaseDefinitions
    namesUnique := by decide
    fresh := by
      intro definition membership
      simp [boolPhaseDefinitions] at membership
      subst definition
      rfl
    bodiesChecked := by
      intro definition membership
      simp [boolPhaseDefinitions] at membership
      subst definition
      exact bool_implementation_check
    combinedNamesUnique := by decide }

def constructorPhaseValidation :
    RecursivePhaseValidation boolPhaseValidation.environment :=
  { definitions := constructorPhaseDefinitions
    namesUnique := by decide
    fresh := by
      intro definition membership
      simp [constructorPhaseDefinitions] at membership
      rcases membership with rfl | rfl
      · rfl
      · rfl
    bodiesChecked := by
      intro definition membership
      simp [constructorPhaseDefinitions] at membership
      rcases membership with rfl | rfl
      · exact true_has_type
      · exact false_has_type
    combinedNamesUnique := by
      simp [RecursivePhaseValidation.environment, boolPhaseValidation,
        boolPhaseDefinitions, constructorPhaseDefinitions,
        boolDefinition, trueDefinition, falseDefinition]
      decide }

/-- Seal the complete two-phase block from its implementation proofs. -/
def sealEnvironment : ValidatedEnv definitions := by
  have constructorHistory :
      ValidationHistory constructorPhaseValidation.definitions
        boolPhaseValidation.environment constructorPhaseValidation.environment := by
    simpa using
      (ValidationHistory.cons (remaining := []) constructorPhaseValidation
        (ValidationHistory.nil constructorPhaseValidation.environment))
  have fullHistory :
      ValidationHistory
        (boolPhaseValidation.definitions ++ constructorPhaseValidation.definitions)
        Environment.empty constructorPhaseValidation.environment :=
    ValidationHistory.cons boolPhaseValidation constructorHistory
  refine ⟨constructorPhaseValidation.environment, ?_⟩
  simpa [definitions, boolPhaseValidation, constructorPhaseValidation] using fullHistory

def validatedEnv : ValidatedEnv definitions := sealEnvironment

theorem validatedEnv_environment :
  validatedEnv.environment = boolEnvironment := by
  apply Environment.eq_of_definitions
  rfl

/-- Recursive induction is available after the complete block is sealed. -/
theorem true_membership_bool :
    Membership validatedEnv.environment []
      (.const trueName) (.const boolName) := by
  apply recursive_induction validatedEnv
  rw [validatedEnv_environment]
  decide

/-- Likewise, `false : Bool` follows only from the sealed environment. -/
theorem false_membership_bool :
    Membership validatedEnv.environment []
      (.const falseName) (.const boolName) := by
  apply recursive_induction validatedEnv
  rw [validatedEnv_environment]
  decide

/-- Recursive names unfold only after receiving an argument. -/
theorem bool_unfolds_when_applied
    (argument : Term) :
    ReducesOne validatedEnv.environment []
      (.app (.const boolName) argument) (.app boolBody argument) := by
  apply unfold_applied validatedEnv
  rw [validatedEnv_environment]
  decide

end FixedPoint.Bool
