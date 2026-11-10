import LambdaStar.NatTest

namespace LambdaStar.BoolTest

open NatTest
open NatTest.NamedTerm

def bool : NamedTerm := .const "Bool"
def assumedBool : NamedTerm := .const "BoolAssumed"
def trueValue : NamedTerm := .const "true"
def falseValue : NamedTerm := .const "false"

private def boolCore (boolean : NamedTerm) : NamedTerm :=
  .lam "P" (.lam "t" (.lam "f"
    (.app (.app .star (.app (.var "P") boolean))
      (boolean.apps
        [.lam "a" (.app .star (.app (.var "P") (.var "a"))),
         .app (.app .star (.app (.var "P") trueValue)) (.var "t"),
         .app (.app .star (.app (.var "P") falseValue)) (.var "f")]))))

/--
The explicitly expanded body:

`Bool b P t f = * (P b) (b (λa. * (P a)) (* (P true) t) (* (P false) f))`.
-/
def boolNamed : NamedTerm :=
  .lam "b" (boolCore (.var "b"))

/--
The proposed self-annotated variant. Expanding `λb : BoolAssumed. t`
replaces `b` by `BoolAssumed b` throughout `t`; it does not add a hypothesis.
-/
def assumedBoolNamed : NamedTerm :=
  typedLam "b" assumedBool (boolCore (.var "b"))

/-- The Bool functional with its recursive projector represented by a μ variable. -/
def recursiveBoolFunctionalNamed : NamedTerm :=
  typedLam "b" (.var "Bool") (boolCore (.var "b"))

/-- `μBool. λb : Bool. ...`. -/
def recursiveBoolNamed : NamedTerm :=
  .mu "Bool" recursiveBoolFunctionalNamed

/-- Corrected nullary constructor: `true = λP. λt. λf. t`. -/
def trueNamed : NamedTerm :=
  .lam "P" (.lam "t" (.lam "f" (.var "t")))

/-- Corrected nullary constructor: `false = λP. λt. λf. f`. -/
def falseNamed : NamedTerm :=
  .lam "P" (.lam "t" (.lam "f" (.var "f")))

def boolBody : Term := boolNamed.compile []
def assumedBoolBody : Term := assumedBoolNamed.compile []
def recursiveBoolFunctional : Term :=
  recursiveBoolFunctionalNamed.compile ["Bool"]
def recursiveBoolTerm : Term := recursiveBoolNamed.compile []
def trueBody : Term := trueNamed.compile []
def falseBody : Term := falseNamed.compile []

private theorem boolBody_closed : boolBody.Closed := by native_decide
private theorem assumedBoolBody_closed : assumedBoolBody.Closed := by native_decide
theorem recursiveBoolFunctional_guarded : recursiveBoolFunctional.MuBodyGuarded := by
  native_decide
theorem recursiveBoolTerm_closed : recursiveBoolTerm.Closed := by native_decide
private theorem trueBody_closed : trueBody.Closed := by native_decide
private theorem falseBody_closed : falseBody.Closed := by native_decide

def environment : DefEnv where
  defs name :=
    if name = "Bool" then some boolBody
    else if name = "true" then some trueBody
    else if name = "false" then some falseBody
    else none
  closed name body definition := by
    change (if name = "Bool" then some boolBody
      else if name = "true" then some trueBody
      else if name = "false" then some falseBody
      else none) = some body at definition
    split at definition
    · cases definition
      exact boolBody_closed
    · split at definition
      · cases definition
        exact trueBody_closed
      · split at definition
        · cases definition
          exact falseBody_closed
        · contradiction

def assumedEnvironment : DefEnv where
  defs name :=
    if name = "BoolAssumed" then some assumedBoolBody
    else if name = "true" then some trueBody
    else if name = "false" then some falseBody
    else none
  closed name body definition := by
    change (if name = "BoolAssumed" then some assumedBoolBody
      else if name = "true" then some trueBody
      else if name = "false" then some falseBody
      else none) = some body at definition
    split at definition
    · cases definition
      exact assumedBoolBody_closed
    · split at definition
      · cases definition
        exact trueBody_closed
      · split at definition
        · cases definition
          exact falseBody_closed
        · contradiction

def boolTerm : Term := bool.compile []
def assumedBoolTerm : Term := assumedBool.compile []
def probeVar : Term := .bvar 0
def boolBoolVariable : Term := .app boolTerm (.app boolTerm probeVar)
def boolVariable : Term := .app boolTerm probeVar
def trueTerm : Term := trueValue.compile []
def falseTerm : Term := falseValue.compile []
def boolBoolTrue : Term := .app boolTerm (.app boolTerm trueTerm)
def boolTrue : Term := .app boolTerm trueTerm
def boolBoolFalse : Term := .app boolTerm (.app boolTerm falseTerm)
def boolFalse : Term := .app boolTerm falseTerm
def assumedBoolBoolVariable : Term :=
  .app assumedBoolTerm (.app assumedBoolTerm probeVar)
def assumedBoolVariable : Term := .app assumedBoolTerm probeVar

namespace Exploration

/-- All contextual stage-0 β/δ/starred-idempotence successors. -/
def oneSteps (Δ : DefEnv) : Term → List Term
  | .bvar _ => []
  | .const name => Δ.defs name |>.toList
  | .star => []
  | .lam body => (oneSteps Δ body).map .lam
  | .mu body => body.unfoldMu :: (oneSteps Δ body).map .mu
  | term@(.app function argument) =>
      let root := match function with
        | .lam body => [body.instantiate argument]
        | _ => match term with
          | .app (.app .star u) (.app (.app .star u') inner) =>
              if u = u' then [.app (.app .star u) inner] else []
          | _ => []
      root ++ (oneSteps Δ function).map (.app · argument) ++
        (oneSteps Δ argument).map (.app function)

def reachable (Δ : DefEnv) : Nat → List Term → Term → Bool
  | 0, frontier, target => frontier.contains target
  | depth + 1, frontier, target =>
      frontier.contains target ||
        reachable Δ depth (frontier.flatMap (oneSteps Δ) |>.eraseDups) target

/-- No direct path appears in the first four stage-0 reductions. -/
theorem no_short_idempotence_path :
    reachable environment 4 [boolBoolVariable] boolVariable = false := by
  native_decide

/-- Even at `true`, no path appears within six arbitrary stage-0 reductions. -/
theorem no_short_true_idempotence_path :
    reachable environment 6 [boolBoolTrue] boolTrue = false := by
  native_decide

/-- Even at `false`, no path appears within six arbitrary stage-0 reductions. -/
theorem no_short_false_idempotence_path :
    reachable environment 6 [boolBoolFalse] boolFalse = false := by
  native_decide

/-- Self-annotation does not create a short idempotence reduction either. -/
theorem no_short_assumed_idempotence_path :
    reachable assumedEnvironment 4
      [assumedBoolBoolVariable] assumedBoolVariable = false := by
  native_decide

end Exploration

/-- The pointwise idempotence question. -/
def BoolIsPointwiseIdempotent : Prop :=
  Reduces environment boolBoolVariable boolVariable

/-- The corresponding closed idempotence certificate. -/
def BoolIsIdempotent : Prop := Idempotent environment boolTerm

/-- Idempotence of the proposed `λb : Bool` variant. -/
def AssumedBoolIsIdempotent : Prop :=
  Idempotent assumedEnvironment assumedBoolTerm

/--
The body goal generated by μ-induction. Its assumption list contains the
recursive Bool projector whose idempotence may be used contextually.
-/
def RecursiveBoolBodyIdempotentAt (stage : Nat) : Prop :=
  GuardedInductiveIdempotent environment [recursiveBoolTerm] stage
    recursiveBoolFunctional.unfoldMu

/-- The complete inductive Bool goal, with no undischarged assumptions. -/
def RecursiveBoolIsInductivelyIdempotent : Prop :=
  GuardedIdempotentByInduction environment recursiveBoolTerm

theorem recursiveBool_bodyIdempotentAt (stage : Nat) :
    RecursiveBoolBodyIdempotentAt stage := by
  change GuardedInductiveIdempotent environment
    [.mu recursiveBoolFunctional] stage recursiveBoolFunctional.unfoldMu
  exact .underAssumptions
    (unfoldMu_idempotentAssumingMu environment stage recursiveBoolFunctional)

theorem recursiveBool_inductivelyIdempotent
    (stage : Nat) :
    GuardedInductiveIdempotent environment [] stage recursiveBoolTerm := by
  change GuardedInductiveIdempotent environment [] stage
    (.mu recursiveBoolFunctional)
  exact .mu recursiveBoolFunctional_guarded
    (recursiveBool_bodyIdempotentAt stage)

theorem recursiveBool_isInductivelyIdempotent :
    RecursiveBoolIsInductivelyIdempotent :=
  ⟨0, recursiveBool_inductivelyIdempotent 0⟩

/-- The recursive Bool projector passes inductive star-checking. -/
theorem star_recursiveBool :
    ExtendedStep environment 1
      (.app .star recursiveBoolTerm) recursiveBoolTerm :=
  inductiveStarChecking recursiveBoolTerm_closed
    (recursiveBool_inductivelyIdempotent 0)

end LambdaStar.BoolTest
