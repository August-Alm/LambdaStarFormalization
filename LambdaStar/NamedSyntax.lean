import LambdaStar.Confluence

namespace LambdaStar

/-- Readable named presentation of the core calculus. -/
inductive NamedTerm where
  | var : String → NamedTerm
  | const : Const → NamedTerm
  | lam : String → NamedTerm → NamedTerm
  | app : NamedTerm → NamedTerm → NamedTerm
  | star : NamedTerm
  deriving DecidableEq, Repr

namespace NamedTerm

def apps : NamedTerm → List NamedTerm → NamedTerm :=
  List.foldl app

/-- Capture-avoiding substitution for the globally fresh example names. -/
def subst (name : String) (replacement : NamedTerm) : NamedTerm → NamedTerm
  | var variableName => if variableName = name then replacement else var variableName
  | const constant => const constant
  | lam binder body =>
      if binder = name then lam binder body else lam binder (subst name replacement body)
  | app function argument =>
      app (subst name replacement function) (subst name replacement argument)
  | star => star

def indexOf (name : String) : List String → Nat
  | [] => 0
  | binder :: binders =>
      if binder = name then 0 else indexOf name binders + 1

def compile (context : List String) : NamedTerm → Term
  | var name => .bvar (indexOf name context)
  | const name => .const name
  | lam binder body => .lam (compile (binder :: context) body)
  | app function argument => .app (compile context function) (compile context argument)
  | star => .star

/-- Package a self-indexed family as the ordinary lambda `λx. family x`. -/
def self (binder : String) (family : NamedTerm) : NamedTerm :=
  lam binder (.app family (.var binder))

/-- `λx : A. t = λx. t{x := A x}`. -/
def typedLam (binder : String) (type body : NamedTerm) : NamedTerm :=
  lam binder (subst binder (.app type (.var binder)) body)

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
    (.app (subst argumentBinder checkedArgument codomain)
      (.app (.var functionBinder) checkedArgument)))

end NamedTerm

end LambdaStar
