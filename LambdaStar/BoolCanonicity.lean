import LambdaStar.BoolTest

namespace LambdaStar.BoolCanonicity

def junkName : Const := "junk"

def signatures : List RecursiveSignature :=
  BoolTest.signatures ++ [⟨junkName, .const BoolTest.boolName, by decide⟩]

def junkBody : RecursiveBody :=
  ⟨junkName, .const junkName, by decide⟩

def junkBodies : List RecursiveBody := [junkBody]

/--
The historical unsafe context accepted a self-named implementation as Bool.
This theorem records the exploit, but it cannot be used by `ChecksRecursivePhase`,
whose realization context excludes all names implemented in that phase.
-/
theorem unsafe_junk_has_type : ChecksImplementation
  (DefEnv.empty.extend BoolTest.typeBodies)
  (RecursiveSignature.context signatures)
    (RecursiveSignature.context signatures)
    junkName (.const junkName) (.const BoolTest.boolName) := by
  apply ChecksImplementation.namedSelf
  · rfl
  · apply Checks.certified
    have deltaReduction : Step (DefEnv.empty.extend BoolTest.typeBodies) 0
        (.app (.const BoolTest.boolName) (.const junkName))
        (.app BoolTest.boolBody (.const junkName)) := .delta (by rfl)
    have selfReduction : Step (DefEnv.empty.extend BoolTest.typeBodies) 0
        (.app BoolTest.boolBody (.const junkName))
        (.app
          ((match BoolTest.boolBody with
            | .iota body => body
            | _ => .star).instantiate
            (.const junkName))
          (.const junkName)) := by
      simp [BoolTest.boolBody, BoolTest.boolBodyNamed]
      exact Step.selfInstantiation
    have signatureAssumption : ContextEquiv
        (DefEnv.empty.extend BoolTest.typeBodies)
        (RecursiveSignature.context signatures)
        (.app (.const BoolTest.boolName) (.const junkName))
        (.const junkName) := by
      apply ContextEquiv.assumption
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
