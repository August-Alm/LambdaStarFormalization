# LambdaStar

We introduce the lambda-star calculus, a very simple extension of the untyped
lambda calculus. By identifying idempotents in this calculus with types, we
can give an operational interpretation of type checking in System Fω, and
extensions involving dependent types. Allowing mutually recursive definitions
adds inductive types, including dependent GADTs.

## Introduction

The correspondence between simply typed lambda calculus and cartesian
closed categories is well-known. Maybe somewhat less known, is that every
such category equipped with an object U and a retract of the mapping space
U^U to U gives a model of the untyped lambda calculus. We can interpret the
untyped lambda calculus in the “unityped” fragment of all terms of type
U. Still less known, is Dana Scott’s proof that every interpretation of the
untyped lambda calculus arises in this way. In what follows, we shall
avoid technicalities about equivalence and freely write = for all nuances of
identification. Dana Scott’s proof proceeds as follows. Consider the category
which has as objects the untyped lambda terms A that (in the interpretation)
are idempotent, A = λx.(A (A x)). Let a morphism A → B be an untyped
term f for which (in the interpretation) f = λx.(B (f (A x))). The identity
morphisms are just idA = A and compositions are by f ◦ g = λx.( f (g x)).
The formulas
```text
A × B = λu.λz.((z (A (u λx.λ y.x))) (B (u λx.λ y.y)))
```
and
```text
A → B = λ f .λx.(B (f (A x)))
```
gives it a cartesian closed structure. From this category we now have an
interpretation of the typed lambda calculus. A term t of type A is a term such
that t = (A t). Finally, the object U = λx.x is like an “any” type, such that
U → U is a retract of U, and from it we recover the untyped interpretation
that we started with.

The category devised in the proof can be regarded as a kind of operational
type theory. We can forget about a specific interpretation, and talk of types
as untyped lambda terms A for which A and A ◦ A are beta equivalent. This
theory of types is operational in the sense that instead of ordinary typing
judgments, we have a single rule – beta reduction – that can check if a term
t has type A, by computationally verifying that t and (A t) are equivalent.
We can give an operational semantics to typing judgments.

The types expressible in this way are in some ways very rich. For example, we
have dependent products (just allow B in the formula for A → B displayed
above to depend on x), singleton types (constant functions), and a natural
notion of subtyping (having t = (A t) we can still have t = (B t); e.g., all types
are subtypes of the “any” type U). However, the types are also rather limited.
In particular, we do not have coproducts, making it impossible to define types
corresponding to standard algebraic data types, and no notion of a kind or
type-of-types, which makes polymorphism seem intractable to express. The present project is an attempt to at finding a simple and well-behaved conservative extension of the untyped lambda calculus, where the
types-as-idempotents perspective can incorporate polymorphism.

## The lambda-star calculus

The lambda-star calculus extends the untyped lambda calculus with a single
constant *:
```text
t, u ::= x | λx.t | (t u) | *
```
We shall freely use standard conventions and terminology familiar from
treatments of the lambda calculus. We will also use the convention that
parentheses of repeated applications can be simplified, and write, e.g., (f x y)
instead of ((f x) y).
Here are the reduction rules:

_lambda-application_

```text
(λx.t u) ↦ t{x := u}
```
This rule is beta-reduction in the lambda calculus.

_starred-idempotence_

```text
(* u (* u t)) ↦ (* u t)
```
for all u and t. In other words, (* u) is idempotent for all u.

_star-checking_
```text
(* u) ↦ u
```
if λx.(u (u x)) reduces in finitely many steps to λx.(u x).
In other words, if u is idempotent, then (∗ u) reduces to u.

We remark that the reduction rules are non-deterministic, which is to say that
we do not impose any reduction order. We shall write ≃ for the induced equivalence relation. Note that we are not imposing any η-equivalence.

It follows from the starred-idempotence rule that λx.(* u (* u x)) reduces
to λx.(* u x). The star-checking rule then implies (* (* u)) ↦ (* u). Hence
λx.(* (* x)) reduces to λx.(* x). Again applying the star-checking rule, we
deduce (* *) ↦ *.

## Operational semantics for type systems

Consider a Church-style System Fω.
```text
t, u ::= x | λx : T.t | ΛX : k | (t u) | (t U)
T, U ::= X | ΛX : k.T | (T U) | T → U | ∀X : k.T
k, k′
::= * | k → k′
```
We shall argue that it is possible to map this grammar to the lambda-star
calculus, in such a way that type derivations can be verified correct by
reduction in the lambda-star calculus.

```text
[x] = x
[λx : T.t] = λx.[t]{x := ([T] x)}
[ΛX : k.t] = λX.[t]{X := ([k] X)}
[X] = X
[ΛX : k.T] = λX.[T]{X := ([k] X)}
[∀X : k.T] = λt.λX.([T] (t X)){X := ([k] X)}
[T → U] = λ f .λx.([U] (f ([T] x)))
[*] = *
[k → k′] = λF.λX.([k′] (F ([k] X)))
```
All forms of application are interpreted as applications.
For example, the type constructor ΛA : *.A → A , is interpreted by
```text
λA.λf.λx.(* A (f (* A x)))
```
while the quantified type ∀A : *.A → A is interpreted by
```text
λf.λA.λx.(* A (f (* A) (* A x)))
```
The polymorphic identity function, that ordinarily would have been written,
ΛA : *.λx : A.x, corresponds to
λA.λx.(* A x).
Checking this term against ∀A : *.A → A gives, after beta reduction,
```text
λA.λf.λx.(* A (* A (* A x)))
```
Two uses of the starred-idempotence rule reduces this down to the expression
for the polymorphic identity, verifying the type checking. The star-checking
rule ensures that we can instantiate the variable A with a particular type (i.e,
with an idempotent), and preserve the result of the type check.

Note that our translation expands into eta-long form. For example,
```text
[λ f : A → A. f] = λf.λx.(A (f (A x)))
```
We make the following conjecture: Let t be an Fω term and let T be a well-formed Fω type. Then ([T] [t]) ≃ [t] in the lambda-star calculus if and
only if the judgment ⊢ t : T can be proven in Fω. Similarly, for an Fω kind k,
([k] [T]) ≃ [T] if and only if ⊢ T : k can be proven in Fω.

Note that in lambda-star we have (* *) ≃ *, i.e., type-in-type, which is
famously wrought with logical inconsistencies. However, in Fω we cannot even
posit * : * because terms, types and kinds are syntactically different.

The interpretation in the lambda-star calculus goes through almost with-
out change, if we add dependent products. One must only take care and

“annotate” the variable occurrences in the codomain:
```text
[Πx : U.T] = λf.λx.([T]{x := ([U] x)} (f ([U] x)))
```
We believe that the interpretation of Fω can be extended to the full Calculus of Constructions.

## Inductive types

We here sketch how one may encode inductive data types by extending the
lambda-star calculus with mutually recursive definitions. The recipe is a direct
transpose of the self-type system introduced by Stump and Fu.

Lets introduce some syntax sugar and write λx : U.t for λx.t{x := (U x)}.
We shall also freely use the notation A → B = λ f .λx.(B (f (A x))) and its
dependent generalization
```text
(x : A) → B = λf.λx.(B{x := (A x)} (f (A x)))
```
Jumping straight to it, the encoding of the type that in a standard functional
programming language might have been written
```text
data Nat = succ Nat | zero
```
is given by the following three mutually recursive terms:
```text
Nat =
  λn.
  λP : Nat → *.
  λs : (k : Nat) → (P (succ k)).
  λz : (P zero).
  (P n (n P s z))

succ =
  λn : Nat.
  λP : Nat → *.
  λs : (k : Nat) → (P (succ k)).
  λz : (P zero).
  (s n)

zero =
  λP : Nat → *.
  λs : (k : Nat) → (P (succ k)).
  λz : (P zero).
  z
```

### Recursive projector binder

The Lean formalization also studies an explicit least-fixed-point binder:

```text
t, u ::= ... | μX.t

μX.F(X) ↦ F(μX.F(X))
```

Unfolding alone does not provide the induction hypothesis needed to prove that
a recursive projector is idempotent. The formalization therefore keeps a
separate inductive-idempotence judgment. While checking the body of `μX.F(X)`,
that judgment permits the contextual contraction

```text
X (X t) ↦ X t
```

and discharges the assumption only when the recursive variable is used in an
admissible projector position. The current concrete check accepts occurrences
at the head of a projector application or beneath a starred projector. A
closed guarded certificate licenses `* (μX.F(X)) ↦ μX.F(X)` in an extended
reduction relation.

This extension is intentionally kept separate from the original `Step`
relation. `LambdaStar.BoolTest` and `LambdaStar.NatTest` contain guarded
`μBool` and `μNat` encodings with complete inductive idempotence certificates.
The Nat constructors remain deterministic recursive environment entries; only
the Nat projector requires the fixed-point induction rule. The extended
relation is stable under substitution and stage lifting, and its principal
interaction with starred idempotence is joinable. Full confluence remains
conditional, as it does for the original relation.

## References

References
[1] Peng Fu and Aaron Stump. “Self Types for Dependently Typed Lambda
Encodings”. In: Rewriting and Typed Lambda Calculi: Joint International
Conferences, RTA and TLCA. 2014, pp. 224–239.

[2] Dana S. Scott. “Relating Theories of the λ-Calculus”. In: To H. B. Curry:
Essays on Combinatory Logic, Lambda Calculus and Formalism. Ed. by
J. P. Seldin and J. R. Hindley. Academic Press, 1980, pp. 403–450.

[3] Paul Taylor. “Recursive Domains, Indexed Category Theory and Polymorphism”.
PhD thesis. Cambridge, 1987.