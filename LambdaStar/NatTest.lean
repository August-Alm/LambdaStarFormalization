import LambdaStar.Confluence

namespace LambdaStar.NatTest

/-!
This file is an executable formalization of the mutually recursive `Nat`,
`succ`, and `zero` example from the README. Named syntax keeps the displayed
formulas readable; `compile` translates it to the de Bruijn representation.
-/

inductive NamedTerm where
  | var : String → NamedTerm
  | const : Const → NamedTerm
  | lam : String → NamedTerm → NamedTerm
  | mu : String → NamedTerm → NamedTerm
  | app : NamedTerm → NamedTerm → NamedTerm
  | star : NamedTerm
  deriving DecidableEq, Repr

namespace NamedTerm

def apps : NamedTerm → List NamedTerm → NamedTerm :=
  List.foldl app

/-- Capture-avoiding substitution for the globally fresh names used below. -/
def subst (name : String) (replacement : NamedTerm) : NamedTerm → NamedTerm
  | var variableName => if variableName = name then replacement else var variableName
  | const constant => const constant
  | lam binder body =>
      if binder = name then lam binder body else lam binder (subst name replacement body)
    | mu binder body =>
      if binder = name then mu binder body else mu binder (subst name replacement body)
  | app function argument =>
      app (subst name replacement function) (subst name replacement argument)
  | star => star

private def indexOf (name : String) : List String → Nat
  | [] => 0
  | binder :: binders =>
      if binder = name then 0 else indexOf name binders + 1

def compile (context : List String) : NamedTerm → Term
  | var name => .bvar (indexOf name context)
  | const name => .const name
  | lam binder body => .lam (compile (binder :: context) body)
  | mu binder body => .mu (compile (binder :: context) body)
  | app function argument => .app (compile context function) (compile context argument)
  | star => .star

/-- `λx : A. t = λx. t{x := A x}`. -/
def typedLam (binder : String) (type body : NamedTerm) : NamedTerm :=
  lam binder (body.subst binder (.app type (.var binder)))

/-- `[A → B] = λf. λx. B (f (A x))`. -/
def arrow (functionBinder argumentBinder : String) (domain codomain : NamedTerm) :
    NamedTerm :=
  lam functionBinder (lam argumentBinder
    (.app codomain (.app (.var functionBinder) (.app domain (.var argumentBinder)))))

/-- `[Πx : A. B] = λf. λx. B{x := A x} (f (A x))`. -/
def pi (functionBinder argumentBinder : String) (domain codomain : NamedTerm) :
    NamedTerm :=
  let checkedArgument := .app domain (.var argumentBinder)
  lam functionBinder (lam argumentBinder
    (.app (codomain.subst argumentBinder checkedArgument)
      (.app (.var functionBinder) checkedArgument)))

end NamedTerm

open NamedTerm

def nat : NamedTerm := .const "Nat"
def succ : NamedTerm := .const "succ"
def zero : NamedTerm := .const "zero"

private def natToStar (suffix : String) : NamedTerm :=
  arrow ("fNatStar" ++ suffix) ("xNatStar" ++ suffix) nat .star

private def stepType (predicate : NamedTerm) (suffix : String) : NamedTerm :=
  pi ("fStep" ++ suffix) ("kStep" ++ suffix) nat
    (.app predicate (.app succ (.var ("kStep" ++ suffix))))

/-- The README's `Nat` body, including every projector inserted by `:`. -/
def natNamed : NamedTerm :=
  .lam "nNat"
    (typedLam "pNat" (natToStar "Nat")
      (typedLam "sNat" (stepType (.var "pNat") "Nat")
        (typedLam "zNat" (.app (.var "pNat") zero)
          (.app (.app (.var "pNat") (.var "nNat"))
            ((NamedTerm.var "nNat").apps
              [.var "pNat", .var "sNat", .var "zNat"])))))

/-- The Nat functional with its recursive projector represented by a μ variable. -/
def recursiveNatFunctionalNamed : NamedTerm :=
  typedLam "nNatMu" (.var "Nat")
    (typedLam "pNatMu"
      (arrow "fNatStarMu" "xNatStarMu" (.var "Nat") .star)
      (typedLam "sNatMu"
        (pi "fStepMu" "kStepMu" (.var "Nat")
          (.app (.var "pNatMu") (.app succ (.var "kStepMu"))))
        (typedLam "zNatMu" (.app (.var "pNatMu") zero)
          (.app (.app (.var "pNatMu") (.var "nNatMu"))
            ((NamedTerm.var "nNatMu").apps
              [.var "pNatMu", .var "sNatMu", .var "zNatMu"])))))

/-- `μNat. λn : Nat. ...`. -/
def recursiveNatNamed : NamedTerm :=
  .mu "Nat" recursiveNatFunctionalNamed

/-- The README's `succ` body, including every projector inserted by `:`. -/
def succNamed : NamedTerm :=
  typedLam "nSucc" nat
    (typedLam "pSucc" (natToStar "Succ")
      (typedLam "sSucc" (stepType (.var "pSucc") "Succ")
        (typedLam "zSucc" (.app (.var "pSucc") zero)
          (.app (.var "sSucc") (.var "nSucc")))))

/-- The README's `zero` body, including every projector inserted by `:`. -/
def zeroNamed : NamedTerm :=
  typedLam "pZero" (natToStar "Zero")
    (typedLam "sZero" (stepType (.var "pZero") "Zero")
      (typedLam "zZero" (.app (.var "pZero") zero) (.var "zZero")))

def natBody : Term := natNamed.compile []
def recursiveNatFunctional : Term :=
  recursiveNatFunctionalNamed.compile ["Nat"]
def recursiveNatTerm : Term := recursiveNatNamed.compile []
def succBody : Term := succNamed.compile []
def zeroBody : Term := zeroNamed.compile []

private theorem natBody_closed : natBody.Closed := by native_decide
theorem recursiveNatFunctional_guarded : recursiveNatFunctional.MuBodyGuarded := by
  native_decide
theorem recursiveNatTerm_closed : recursiveNatTerm.Closed := by native_decide
private theorem succBody_closed : succBody.Closed := by native_decide
private theorem zeroBody_closed : zeroBody.Closed := by native_decide

/-- One deterministic environment containing all three recursive equations. -/
def environment : DefEnv where
  defs name :=
    if name = "Nat" then some natBody
    else if name = "succ" then some succBody
    else if name = "zero" then some zeroBody
    else none
  closed name body definition := by
    change (if name = "Nat" then some natBody
      else if name = "succ" then some succBody
      else if name = "zero" then some zeroBody
      else none) = some body at definition
    split at definition
    · cases definition
      exact natBody_closed
    · split at definition
      · cases definition
        exact succBody_closed
      · split at definition
        · cases definition
          exact zeroBody_closed
        · contradiction

/-- The constructor equations with the μ-based Nat projector. -/
def recursiveEnvironment : DefEnv where
  defs name :=
    if name = "Nat" then some recursiveNatTerm
    else if name = "succ" then some succBody
    else if name = "zero" then some zeroBody
    else none
  closed name body definition := by
    change (if name = "Nat" then some recursiveNatTerm
      else if name = "succ" then some succBody
      else if name = "zero" then some zeroBody
      else none) = some body at definition
    split at definition
    · cases definition
      exact recursiveNatTerm_closed
    · split at definition
      · cases definition
        exact succBody_closed
      · split at definition
        · cases definition
          exact zeroBody_closed
        · contradiction

def natTerm : Term := nat.compile []
def succTerm : Term := succ.compile []
def zeroTerm : Term := zero.compile []
def natArrowNat : Term := (arrow "fCheck" "xCheck" nat nat).compile []

def checkedSucc : Term := .app natArrowNat succTerm
def checkedZero : Term := .app natTerm zeroTerm

namespace Exploration

/-- All stage-0 β/δ/starred-idempotence successors of a term. -/
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

def reachableBeam (Δ : DefEnv) (width : Nat) : Nat → List Term → Term → Bool
  | 0, frontier, target => frontier.contains target
  | depth + 1, frontier, target =>
      frontier.contains target ||
        reachableBeam Δ width depth
          (frontier.flatMap (oneSteps Δ) |>.eraseDups |>.take width) target

def probeVar : Term := .bvar 0
def natNatVariable : Term := .app natTerm (.app natTerm probeVar)
def natVariable : Term := .app natTerm probeVar

/-- Exhaustive stage-0 search finds no path of at most four reductions. -/
theorem no_short_nat_idempotence_path :
    reachable environment 4 [natNatVariable] natVariable = false := by
  native_decide

/-- A wider, deeper diagnostic search likewise finds no candidate path. -/
theorem no_beam_nat_idempotence_path :
    reachableBeam environment 20 12 [natNatVariable] natVariable = false := by
  native_decide

end Exploration

/-- Legacy constant-based certificate question retained for comparison. -/
def NatIsIdempotent : Prop := Idempotent environment natTerm

/-- Legacy constant-based pointwise question retained for comparison. -/
def NatIsPointwiseIdempotent : Prop :=
  Reduces environment
    (.app natTerm (.app natTerm (.bvar 0)))
    (.app natTerm (.bvar 0))

/-- Constructor-typing question for the original constant-based encoding. -/
def SuccHasType : Prop := Joinable environment checkedSucc succTerm

/-- Constructor-typing question for the original constant-based encoding. -/
def ZeroHasType : Prop := Joinable environment checkedZero zeroTerm

/-- The body goal generated by μ-induction for the recursive Nat projector. -/
def RecursiveNatBodyIdempotentAt (stage : Nat) : Prop :=
  GuardedInductiveIdempotent recursiveEnvironment [recursiveNatTerm] stage
    recursiveNatFunctional.unfoldMu

/-- The complete inductive Nat goal, with no undischarged assumptions. -/
def RecursiveNatIsInductivelyIdempotent : Prop :=
  GuardedIdempotentByInduction recursiveEnvironment recursiveNatTerm

theorem recursiveNat_bodyIdempotentAt (stage : Nat) :
    RecursiveNatBodyIdempotentAt stage := by
  change GuardedInductiveIdempotent recursiveEnvironment
    [.mu recursiveNatFunctional] stage recursiveNatFunctional.unfoldMu
  exact .underAssumptions
    (unfoldMu_idempotentAssumingMu recursiveEnvironment stage
      recursiveNatFunctional)

theorem recursiveNat_inductivelyIdempotent (stage : Nat) :
    GuardedInductiveIdempotent recursiveEnvironment [] stage recursiveNatTerm := by
  change GuardedInductiveIdempotent recursiveEnvironment [] stage
    (.mu recursiveNatFunctional)
  exact .mu recursiveNatFunctional_guarded
    (recursiveNat_bodyIdempotentAt stage)

theorem recursiveNat_isInductivelyIdempotent :
    RecursiveNatIsInductivelyIdempotent :=
  ⟨0, recursiveNat_inductivelyIdempotent 0⟩

/-- The recursive Nat projector passes inductive star-checking. -/
theorem star_recursiveNat :
    ExtendedStep recursiveEnvironment 1
      (.app .star recursiveNatTerm) recursiveNatTerm :=
  inductiveStarChecking recursiveNatTerm_closed
    (recursiveNat_inductivelyIdempotent 0)

/-- Pointwise idempotence is operational for the certified Nat projector. -/
theorem recursiveNat_idempotence (term : Term) :
    ExtendedStep recursiveEnvironment 1
      (.app recursiveNatTerm (.app recursiveNatTerm term))
      (.app recursiveNatTerm term) :=
  inductiveIdempotence recursiveNatTerm_closed
    (recursiveNat_inductivelyIdempotent 0)

end LambdaStar.NatTest
