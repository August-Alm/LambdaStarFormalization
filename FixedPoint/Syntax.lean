namespace FixedPoint

abbrev Const := String

inductive Term where
  | bvar : Nat → Term
  | const : Const → Term
  | lam : Term → Term → Term
  | app : Term → Term → Term
  | any : Term
  deriving DecidableEq, Repr

namespace Term

/-- Shift free indices at or above `cutoff`. -/
def shift (term : Term) (amount cutoff : Nat := 0) : Term :=
  match term with
  | .bvar index => if cutoff ≤ index then .bvar (index + amount) else .bvar index
  | .const name => .const name
  | .lam annotation body =>
      .lam (annotation.shift amount cutoff) (body.shift amount (cutoff + 1))
  | .app function argument =>
      .app (function.shift amount cutoff) (argument.shift amount cutoff)
  | .any => .any

/-- Replace the variable at `depth`, removing that binder. -/
def substAt (term replacement : Term) (depth : Nat := 0) : Term :=
  match term with
  | .bvar index =>
      if index = depth then replacement.shift depth
      else if depth < index then .bvar (index - 1)
      else .bvar index
  | .const name => .const name
  | .lam annotation body =>
      .lam (annotation.substAt replacement depth)
        (body.substAt replacement (depth + 1))
  | .app function argument =>
      .app (function.substAt replacement depth)
        (argument.substAt replacement depth)
  | .any => .any

/-- Instantiate the outermost variable in a lambda body. -/
def instantiate (body argument : Term) : Term := body.substAt argument

def WellScoped (bound : Nat) : Term → Prop
  | .bvar index => index < bound
  | .const _ => True
  | .lam annotation body => WellScoped bound annotation ∧ WellScoped (bound + 1) body
  | .app function argument => WellScoped bound function ∧ WellScoped bound argument
  | .any => True

instance wellScopedDecidable (bound : Nat) :
    (term : Term) → Decidable (WellScoped bound term)
  | .bvar index => inferInstanceAs (Decidable (index < bound))
  | .const _ => isTrue trivial
  | .lam annotation body =>
      @instDecidableAnd _ _ (wellScopedDecidable bound annotation)
        (wellScopedDecidable (bound + 1) body)
  | .app function argument =>
      @instDecidableAnd _ _ (wellScopedDecidable bound function)
        (wellScopedDecidable bound argument)
  | .any => isTrue trivial

abbrev Closed (term : Term) : Prop := WellScoped 0 term

end Term

structure RecursiveDefinition where
  name : Const
  annotation : Term
  body : Term
  annotationClosed : annotation.Closed
  bodyClosed : body.Closed

structure Environment where
  definitions : List RecursiveDefinition
  namesUnique : (definitions.map (·.name)).Nodup

namespace Environment

def empty : Environment := ⟨[], .nil⟩

def lookup (environment : Environment) (name : Const) : Option RecursiveDefinition :=
  environment.definitions.find? (·.name = name)

def lookupAnnotation (environment : Environment) (name : Const) : Option Term :=
  (environment.lookup name).map (·.annotation)

def lookupBody (environment : Environment) (name : Const) : Option Term :=
  (environment.lookup name).map (·.body)

end Environment

abbrev Context := List Term

namespace Context

/-- Enter a binder, expressing every assumption in the extended scope. -/
def extend (context : Context) (annotation : Term) : Context :=
  annotation.shift 1 :: context.map (Term.shift · 1)

def Lookup (context : Context) (index : Nat) (annotation : Term) : Prop :=
  context[index]? = some annotation

end Context

end FixedPoint
