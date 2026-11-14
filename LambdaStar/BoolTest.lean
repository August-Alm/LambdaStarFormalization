import LambdaStar.NamedSyntax
import LambdaStar.Recursive

namespace LambdaStar.BoolTest

open LambdaStar
open NamedTerm

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def boolName : Const := "Bool"
def trueName : Const := "true"
def falseName : Const := "false"

def predicateTypeNamed : NamedTerm :=
  arrow "predicate" "value" (.const boolName) .star

/-- `ΠP : Bool → *. P true → P false → P b`. -/
def boolFamilyNamed : NamedTerm :=
  pi "eliminate" "P" predicateTypeNamed <|
    arrow "onTrue" "trueProof" (.app (.var "P") (.const trueName)) <|
      arrow "onFalse" "falseProof" (.app (.var "P") (.const falseName))
        (.app (.var "P") (.var "b"))

/-- The self-indexed projector `λb. (ΠP : Bool → *. P true → P false → P b) b`. -/
def boolBodyNamed : NamedTerm :=
  self "b" boolFamilyNamed

/-- `λP : Bool → *. λt : P true. λf : P false. t`. -/
def trueBodyNamed : NamedTerm :=
  typedLam "P" predicateTypeNamed <|
    typedLam "t" (.app (.var "P") (.const trueName)) <|
      typedLam "f" (.app (.var "P") (.const falseName)) (.var "t")

/-- `λP : Bool → *. λt : P true. λf : P false. f`. -/
def falseBodyNamed : NamedTerm :=
  typedLam "P" predicateTypeNamed <|
    typedLam "t" (.app (.var "P") (.const trueName)) <|
      typedLam "f" (.app (.var "P") (.const falseName)) (.var "f")

def boolFamily : Term := boolFamilyNamed.compile ["b"]
def boolBody : Term := boolBodyNamed.compile []
def trueBody : Term := trueBodyNamed.compile []
def falseBody : Term := falseBodyNamed.compile []

theorem boolBody_closed : boolBody.Closed := by decide
theorem trueBody_closed : trueBody.Closed := by decide
theorem falseBody_closed : falseBody.Closed := by decide

def signatures : List RecursiveSignature :=
  [⟨boolName, .star, by decide⟩,
   ⟨trueName, .const boolName, by decide⟩,
   ⟨falseName, .const boolName, by decide⟩]

def typeBodies : List RecursiveBody :=
  [⟨boolName, boolBody, boolBody_closed⟩]

def constructorBodies : List RecursiveBody :=
  [⟨trueName, trueBody, trueBody_closed⟩,
   ⟨falseName, falseBody, falseBody_closed⟩]

theorem bool_has_type : ChecksImplementation DefEnv.empty
    (DefEnv.empty.extend typeBodies)
    (RecursiveSignature.contextWithout signatures (typeBodies.map (·.name)))
    boolName boolBody .star := by
  apply ChecksImplementation.recursiveTypeFormation
  · rfl
  · apply Checks.certified
    intro depth
    apply ContextEquiv.starChecking
    apply GuardedSteps.single
    apply GuardedStep.recursiveIdempotenceAt
    · rfl
    · intro guardedDepth
      apply ContextEquiv.contextualStepsTo guardedDepth 10000
      rfl

theorem true_has_type : ChecksImplementation (DefEnv.empty.extend typeBodies)
  ((DefEnv.empty.extend typeBodies).extend constructorBodies)
    (RecursiveSignature.contextWithout signatures
      (constructorBodies.map (·.name)))
    trueName trueBody (.const boolName) := by
  apply ChecksImplementation.namedSelf
  · rfl
  · apply Checks.certified
    intro depth
    apply ContextEquiv.ofContextualStepsEq depth 500
    rfl

theorem false_has_type : ChecksImplementation (DefEnv.empty.extend typeBodies)
  ((DefEnv.empty.extend typeBodies).extend constructorBodies)
    (RecursiveSignature.contextWithout signatures
      (constructorBodies.map (·.name)))
    falseName falseBody (.const boolName) := by
  apply ChecksImplementation.namedSelf
  · rfl
  · apply Checks.certified
    intro depth
    apply ContextEquiv.ofContextualStepsEq depth 500
    rfl

/-- Bool is validated before its body may be unfolded by constructor checks. -/
abbrev TypePhaseCheck : Prop :=
  ChecksRecursivePhase DefEnv.empty signatures typeBodies

/-- Constructor bodies may unfold the already validated Bool body, not themselves. -/
abbrev ConstructorPhaseCheck : Prop :=
  ChecksRecursivePhase (DefEnv.empty.extend typeBodies) signatures constructorBodies

abbrev BlockCheck : Prop :=
  ChecksRecursiveBlock signatures DefEnv.empty
    [typeBodies, constructorBodies]
    ((DefEnv.empty.extend typeBodies).extend constructorBodies)

theorem typePhase_valid : TypePhaseCheck := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro definition membership
    simp [typeBodies] at membership
    subst definition
    rfl
  · intro definition membership
    simp [typeBodies] at membership
    subst definition
    exact ⟨.star, rfl, bool_has_type⟩

theorem constructorPhase_valid : ConstructorPhaseCheck := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro definition membership
    simp [constructorBodies] at membership
    rcases membership with rfl | rfl <;> rfl
  · intro definition membership
    simp [constructorBodies] at membership
    rcases membership with rfl | rfl
    · exact ⟨.const boolName, rfl, true_has_type⟩
    · exact ⟨.const boolName, rfl, false_has_type⟩

theorem block_valid : BlockCheck := by
  refine ⟨.cons typePhase_valid (.cons constructorPhase_valid .nil), ?_⟩
  native_decide

end LambdaStar.BoolTest
