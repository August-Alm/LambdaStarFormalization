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
  cases depth with
  | zero => exact ContextEquiv.zero
  | succ guardedDepth =>
    apply ContextEquiv.ofGuardedStep
    apply GuardedStep.recursiveIdempotenceAt
    · rfl
    · cases guardedDepth with
      | zero =>
        apply ContextEquiv.contextualStepsTo 0 0 100 <;> rfl
      | succ depth =>
        apply ContextEquiv.contextualStepsTo (depth + 1) (depth + 1) 100 <;> rfl

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
