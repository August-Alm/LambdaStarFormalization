# LambdaStar

We introduce the lambda-star calculus, a very simple extension of the untyped
lambda calculus. By identifying idempotents in this calculus with types, we
can propose an operational interpretation of type checking in System Fω, and
extensions involving dependent types. Allowing mutually recursive definitions
extends the proposal to inductive types, including dependent GADTs.

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

## The core calculus

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

### Operational semantics for type systems

Consider a Church-style System Fω.
```text
t, u ::= x | λx : T.t | ΛX : k.t | (t u) | (t U)
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
λA.λx.(* A (* A (* A x)))
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

## Lean formalization and inductive types extension

Our formalization adds self-references and finite recursive
definition environments.

```text
t, u ::= x | c | λx.t | ιx.T | (t u) | *
```

Here `x` ranges over bound variables and `c` ranges over **closure names**.
A closure environment `Δ` associates a name `c` with at most one closed body
`Δ(c)`. Recursive declaration blocks provide finite lists of signatures and
bodies from which these environments are built. A bare name is a stable term:
only an application `c u` exposes the body as `Δ(c) u`. This lets recursive
types and constructors refer to persistent names such as `Bool`, `true`, and
`false` without replacing those names by their implementation bodies.

### Formalized reduction

Reduction is indexed by a natural-number certification stage. At every stage
`n`, the root contractions are:

```text
(λx.t) u             ↦ₙ [u/x]t
(ιx.T) t             ↦ₙ ([t/x]T) t
c u                  ↦ₙ b u                 if Δ(c) = b
(* A) ((* A) t)      ↦ₙ (* A) t
```

The remaining root contraction is **star checking**. It recognizes `A` as a
type projector from an idempotence certificate at the preceding stage:

```text
λx. A (A x) ↦*ₙ λx. A x
----------------------- StarChecking
  * A ↦ₙ₊₁ A
```

Here `↦*ₙ` is the reflexive-transitive closure of `↦ₙ`, at one fixed stage.
Requiring the certificate at stage `n` before adding the contraction at stage
`n + 1` makes the rule well-founded rather than self-justifying. (This stage-indexed rule superceeds the more informal unindexed recursive condition of the introductory description of the core calculus.)

One-step reduction is also closed under every immediate term context:

```text
t ↦ₙ t'                  T ↦ₙ T'
──────────────           ──────────────
λx.t ↦ₙ λx.t'            ιx.T ↦ₙ ιx.T'

t ↦ₙ t'                  u ↦ₙ u'
──────────────           ──────────────
t u ↦ₙ t' u              t u ↦ₙ t u'
```

These four congruence rules together with the five root contractions above are
all constructors of the one-step relation. Every body in `Δ` is closed, and
each name has at most one body.

Operationally, an idempotence certificate is a finite reduction

```text
λx. A (A x) ↦* λx. A x
```

and `*` recognizes such certified projectors. Consequently `A : *` means
`* A ≃ A`: `A` is itself fixed by the universe projector. Certification is
stratified, so a `* A ↦ A` step may use only an idempotence derivation from an
earlier stage.


### Scoped self types

The self type `ιx.T` is also a projector. Applying it to a candidate `t`
specializes the body at that same candidate:

```text
(ιx.T) t ↦ ([t/x]T) t
```

This is what allows an encoded datatype to state an elimination principle
whose result mentions the value being checked.

`Checks Δ Γ t A` is a proof-producing operational typing judgment. Its
soundness theorem yields contextual projector equality:

```text
Checks Δ Γ t A  implies  Γ ⊢ A t ≃ t
```

Self introduction requires the instantiated body:

```text
Γ ⊢ t : [t/x]T
---------------- SelfGen
Γ ⊢ t : ιx.T
```

Self elimination exposes it, and formation checks the body under one fresh
neutral assumption. There is no cyclic rule that assumes the equality being
proved.

### Recursive blocks

A recursive block separates signatures from bodies. Every signature is in
scope for type formation, while value realization omits signatures implemented
in the current phase. Reduction may unfold only bodies validated by earlier
phases. Successful phases extend the environment for later ones.

Implementation checking distinguishes three cases:

1. An ordinary implementation body is checked directly against its declared
  projector.
2. If `A = ιx.T` was validated in an earlier phase, the body for a named closure
  `c : A` is checked against `T[c/x]`.
3. A function returning a named self type is checked pointwise under its domain
  assumption.

The latter two cases preserve the stable closure name instead of substituting
its implementation body. Thus constructor indices remain `P true`, `P zero`,
and `P (succ n)`. Concretely, the body of `succ : Nat → Nat` is checked under
`n : Nat` against the Nat self body at `succ (Nat n)`.

Bool therefore uses:

```text
rec {
  Bool  : * =
    ιb. ΠP : Bool → *. P true → P false → P b

  true  : Bool =
    λP : Bool → *. λt : P true. λf : P false. t

  false : Bool =
    λP : Bool → *. λt : P true. λf : P false. f
}
```

The Bool body is validated first. Constructor validation may unfold that
validated body, but neither constructor may unfold itself. Nat follows the
same two-phase discipline with signatures for `Nat`, `zero`, and `succ`.

Nat uses the full induction projector and supplies the induction hypothesis in
its successor implementation:

```text
rec {
  Nat  : * =
    ιn. ΠP : Nat → *.
      (Πk : Nat. P k → P (succ k)) → P zero → P n

  zero : Nat =
    λP : Nat → *.
    λs : (Πk : Nat. P k → P (succ k)).
    λz : P zero.
    z

  succ : Nat → Nat =
    λn : Nat.
    λP : Nat → *.
    λs : (Πk : Nat. P k → P (succ k)).
    λz : P zero.
    s n (n P s z)
}
```

## Modules

- `Syntax.lean`: terms, arrow projectors, substitution, scoping, and closed
  environments.
- `Reduction.lean`: staged beta, closure application, self instantiation, and
  star reduction.
- `Confluence.lean`: joinability and conditional confluence infrastructure.
- `SelfTyping.lean`: scoped self-type rules, proof-producing contextual
  normalization, and operational soundness.
- `Recursive.lean`: recursive signatures, closure-aware implementation checks,
  and phased body validation.
- `BoolTest.lean` and `NatTest.lean`: annotated recursive declarations.
- `BoolCanonicity.lean`: regression proofs for the self-certifying Bool
  declaration that the phase realization context now excludes.

## Status

The Bool and Nat type phases, constructor phases, and complete recursive blocks
are proved without `sorry`. In particular, the validated declarations establish
`Bool : *`, `true : Bool`, `false : Bool`, `Nat : *`, `zero : Nat`, and
`succ : Nat → Nat`.
The corresponding final theorems are `BoolTest.block_valid` and
`NatTest.block_valid`. Global normalization and unconditional confluence remain separate
metatheoretic questions.

Recursive validation separates assumptions used for type formation from those
allowed to certify implementations. Type formation receives all signatures,
while value realization excludes every name implemented in the current phase.
This prevents a declaration such as `junk : Bool = junk` from certifying itself
with its own signature, and also blocks same-phase mutual self-certification.
`BoolCanonicity.unsafe_junk_has_type` records the old derivation under an
explicitly unsafe context; `junk_signature_excluded` proves that its crucial
equation is absent from the actual phase realization context. A full theorem
that every closed Bool inhabitant is equivalent to `true` or `false` remains to
be proved.

```sh
lake build
```