import LambdaStar.BoolTest

namespace LambdaStar.BoolCanonicity

def junkName : Const := "junk"

def signatures : List RecursiveSignature :=
  BoolTest.signatures ++ [⟨junkName, .const BoolTest.boolName, by decide⟩]

def junkBody : RecursiveBody :=
  ⟨junkName, .const junkName, by decide⟩

def junkBodies : List RecursiveBody := [junkBody]

def etaName : Const := "A"
def etaBody : Term := Term.self (.const etaName)
def etaBodies : List RecursiveBody :=
  [⟨etaName, etaBody, by decide⟩]
def etaEnv : DefEnv := DefEnv.empty.extend etaBodies

/--
Eta recursion is guarded at every finite observation depth. This establishes
idempotence safety, not productivity or the existence of a canonical value.
-/
theorem etaRecursiveFamily_guarded :
    ∀ depth, ContextEquiv DefEnv.empty etaEnv depth []
      (idempotenceLhs (.const etaName))
      (idempotenceRhs (.const etaName)) := by
  intro depth
  apply ContextEquiv.ofGuardedStep
  apply GuardedStep.recursiveIdempotenceAt
  · rfl
  · intro guardedDepth
    apply ContextEquiv.contextualStepsTo guardedDepth 100
    rfl

/--
The historical unsafe context accepted a self-named implementation as Bool.
This theorem records the exploit, but it cannot be used by `ChecksRecursivePhase`,
whose realization context excludes all names implemented in that phase.
-/
theorem unsafe_junk_has_type : ChecksImplementation
  (DefEnv.empty.extend BoolTest.typeBodies)
  (DefEnv.empty.extend BoolTest.typeBodies)
    (RecursiveSignature.context signatures)
    junkName (.const junkName) (.const BoolTest.boolName) := by
  apply ChecksImplementation.namedSelf
  · rfl
  · apply Checks.certified
    intro depth
    have deltaReduction : Step (DefEnv.empty.extend BoolTest.typeBodies) 0
        (.app (.const BoolTest.boolName) (.const junkName))
        (.app BoolTest.boolBody (.const junkName)) := .delta (by rfl)
    have selfReduction : Step (DefEnv.empty.extend BoolTest.typeBodies) 0
        (.app BoolTest.boolBody (.const junkName))
        (.app
          (BoolTest.boolFamily.instantiate (.const junkName))
          (.const junkName)) := by
      change Step (DefEnv.empty.extend BoolTest.typeBodies) 0
        (.app (Term.self BoolTest.boolFamily) (.const junkName))
        (.app
          (BoolTest.boolFamily.instantiate (.const junkName))
          (.const junkName))
      exact Step.beta
    have signatureAssumption : ContextEquiv
        (DefEnv.empty.extend BoolTest.typeBodies)
      (DefEnv.empty.extend BoolTest.typeBodies)
      depth
        (RecursiveSignature.context signatures)
        (.app (.const BoolTest.boolName) (.const junkName))
        (.const junkName) := by
      apply ContextEquiv.ofGuardedStep
      apply GuardedStep.assumption
      simp [signatures, RecursiveSignature.context, BoolTest.signatures]
    exact .trans
      (.symm (.trans
        (ContextEquiv.ofStep deltaReduction)
        (ContextEquiv.ofStep selfReduction)))
      signatureAssumption

/-- The exact equation used by the exploit is absent during realization. -/
theorem junk_signature_excluded :
    (.app (.const BoolTest.boolName) (.const junkName), .const junkName) ∉
      RecursiveSignature.contextWithout signatures (junkBodies.map (·.name)) := by
  decide

theorem distinctConstants_not_joinable
    (distinct : leftName ≠ rightName) :
    ¬Joinable environment (.const leftName) (.const rightName) := by
  intro joinable
  obtain ⟨join, ⟨leftStage, left⟩, ⟨rightStage, right⟩⟩ := joinable
  have equality : Term.const leftName = Term.const rightName :=
    left.const_source.symm.trans right.const_source
  exact distinct (Term.const.inj equality)

theorem junk_not_joinable_true (environment : DefEnv) :
    ¬Joinable environment (.const junkName) (.const BoolTest.trueName) :=
  distinctConstants_not_joinable (by decide)

theorem junk_not_joinable_false (environment : DefEnv) :
    ¬Joinable environment (.const junkName) (.const BoolTest.falseName) :=
  distinctConstants_not_joinable (by decide)

theorem true_not_joinable_false (environment : DefEnv) :
    ¬Joinable environment (.const BoolTest.trueName) (.const BoolTest.falseName) :=
  distinctConstants_not_joinable (by decide)

end LambdaStar.BoolCanonicity
