import LambdaStar.BoolTest

namespace LambdaStar.NatTest

open LambdaStar
open NamedTerm

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def natName : Const := "Nat"
def zeroName : Const := "zero"
def succName : Const := "succ"

def predicateTypeNamed : NamedTerm :=
  arrow "predicate" "value" (.const natName) .star

/-- `[Πk : Nat. P k → P (succ k)]`. -/
def stepTypeNamed : NamedTerm :=
  pi "step" "k" (.const natName) <|
    arrow "induction" "proof" (.app (.var "P") (.var "k"))
      (.app (.var "P") (.app (.const succName) (.var "k")))

/-- `ΠP : Nat → *. (Πk : Nat. P k → P (succ k)) → P zero → P n`. -/
def natFamilyNamed : NamedTerm :=
  pi "eliminate" "P" predicateTypeNamed <|
    arrow "onSucc" "step" stepTypeNamed <|
      arrow "onZero" "base" (.app (.var "P") (.const zeroName))
        (.app (.var "P") (.var "n"))

/-- The self-indexed projector `λn. family(n) n`. -/
def natBodyNamed : NamedTerm :=
  self "n" natFamilyNamed

/-- `λP : Nat → *. λs : step(P). λz : P zero. z`. -/
def zeroBodyNamed : NamedTerm :=
  typedLam "P" predicateTypeNamed <|
    typedLam "s" stepTypeNamed <|
      typedLam "z" (.app (.var "P") (.const zeroName)) (.var "z")

/-- `λn : Nat. λP : Nat → *. λs : step(P). λz : P zero. s n (n P s z)`. -/
def succBodyNamed : NamedTerm :=
  typedLam "n" (.const natName) <|
    typedLam "P" predicateTypeNamed <|
      typedLam "s" stepTypeNamed <|
        typedLam "z" (.app (.var "P") (.const zeroName))
          (apps (.var "s")
            [.var "n", apps (.var "n") [.var "P", .var "s", .var "z"]])

def natFamily : Term := natFamilyNamed.compile ["n"]
def natBody : Term := natBodyNamed.compile []
def zeroBody : Term := zeroBodyNamed.compile []
def succBody : Term := succBodyNamed.compile []

theorem natBody_closed : natBody.Closed := by decide
theorem zeroBody_closed : zeroBody.Closed := by decide
theorem succBody_closed : succBody.Closed := by decide

def signatures : List RecursiveSignature :=
  [⟨natName, .star, by decide⟩,
   ⟨zeroName, .const natName, by decide⟩,
  ⟨succName, Term.arrow (.const natName) (.const natName), by decide⟩]

def typeBodies : List RecursiveBody :=
  [⟨natName, natBody, natBody_closed⟩]

def constructorBodies : List RecursiveBody :=
  [⟨zeroName, zeroBody, zeroBody_closed⟩,
   ⟨succName, succBody, succBody_closed⟩]

theorem nat_has_type : ChecksImplementation DefEnv.empty
    (DefEnv.empty.extend typeBodies)
    (RecursiveSignature.contextWithout signatures (typeBodies.map (·.name)))
    natName natBody .star := by
  apply ChecksImplementation.recursiveTypeFormation
  · rfl
  · apply Checks.certified
    apply ContextEquiv.starChecking
    apply ContextEquiv.recursiveIdempotence
    · rfl
    · native_decide
    · apply ContextEquiv.ofContextualStepsEq 20000
      rfl

theorem zero_has_type : ChecksImplementation (DefEnv.empty.extend typeBodies)
  ((DefEnv.empty.extend typeBodies).extend constructorBodies)
    (RecursiveSignature.contextWithout signatures
      (constructorBodies.map (·.name)))
    zeroName zeroBody (.const natName) := by
  apply ChecksImplementation.namedSelf
  · rfl
  · apply Checks.certified
    apply ContextEquiv.ofContextualStepsEq 1000
    rfl

theorem succ_has_type : ChecksImplementation (DefEnv.empty.extend typeBodies)
  ((DefEnv.empty.extend typeBodies).extend constructorBodies)
    (RecursiveSignature.contextWithout signatures
      (constructorBodies.map (·.name)))
    succName succBody (Term.arrow (.const natName) (.const natName)) := by
  apply ChecksImplementation.namedSelfFunction
  · rfl
  · apply Checks.certified
    apply ContextEquiv.ofContextualStepsEq 2000
    rfl

abbrev TypePhaseCheck : Prop :=
  ChecksRecursivePhase DefEnv.empty signatures typeBodies

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
    exact ⟨.star, rfl, nat_has_type⟩

theorem constructorPhase_valid : ConstructorPhaseCheck := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro definition membership
    simp [constructorBodies] at membership
    rcases membership with rfl | rfl <;> rfl
  · intro definition membership
    simp [constructorBodies] at membership
    rcases membership with rfl | rfl
    · exact ⟨.const natName, rfl, zero_has_type⟩
    · exact ⟨Term.arrow (.const natName) (.const natName), rfl, succ_has_type⟩

theorem block_valid : BlockCheck :=
  .cons typePhase_valid (.cons constructorPhase_valid .nil)

end LambdaStar.NatTest
