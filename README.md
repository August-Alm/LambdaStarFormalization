# LambdaStar

We introduce the lambda-star calculus, a very simple extension of the untyped
lambda calculus. By identifying idempotents in this calculus with types, we
can propose an operational interpretation of type checking in System Fω, and
extensions involving dependent types. Allowing mutually recursive definitions
supports recursive projector encodings such as the Bool and Nat developments
below; a general account of inductive types and dependent GADTs remains a goal.

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
In other words, if u is idempotent, then (* u) reduces to u.

We remark that the reduction rules are non-deterministic, which is to say that
we do not impose any reduction order. We shall write ≃ for the induced equivalence relation. Note that we are not imposing any η-equivalence.

It follows from the starred-idempotence rule that λx.(* u (* u x)) reduces
to λx.(* u x). The star-checking rule then implies (* (* u)) ↦ (* u). Hence
λx.(* (* x)) reduces to λx.(* x). Again applying the star-checking rule, we
deduce (* *) ↦ *.

### Categorical semantics

As a sketch, begin with a cartesian closed category C, its terminal object
I, and a reflexive object U: maps i : U^U → U and j : U → U^U with
j ◦ i = id. This is the usual setting for interpreting the untyped lambda
calculus. By exponential adjunction, every global element u : I → U
determines an endomorphism decode(u) : U → U by transposing j ◦ u.

An interpretation of * is a global element star : I → U. Write
σ = decode(star), so that σ ◦ u interprets (* u). The two additional
requirements are that decode(σ ◦ u) is idempotent for every u, and that
σ ◦ u = u whenever decode(u) is idempotent. These are the categorical
counterparts of starred idempotence and star checking.

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

## Lean formalization and recursive projectors

Our formalization adds finite recursive definition environments.

```text
t, u ::= x | c | λx.t | (t u) | *
```

Here `x` ranges over bound variables and `c` ranges over **closure names**.
A closure environment `Δ` associates a name `c` with at most one closed body
`Δ(c)`. Recursive declaration blocks provide finite lists of signatures and
bodies from which these environments are built. A bare name is a stable term:
only an application `c u` exposes the body as `Δ(c) u`. This lets recursive
types and constructors refer to persistent names such as `Bool`, `true`, and
`false` without replacing those names by their implementation bodies.

### Formalized reduction

The closed computational fragment is indexed by a natural-number certification
stage. At every stage `n`, its root contractions are:

```text
(λx.t) u             ↦ₙ t{x := u}
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
t ↦ₙ t'
──────────────
λx.t ↦ₙ λx.t'

t ↦ₙ t'                  u ↦ₙ u'
──────────────           ──────────────
t u ↦ₙ t' u              t u ↦ₙ t u'
```

These three congruence rules together with the four root contractions above are
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

Typing uses a second, contextual operational relation, `GuardedStep`. It embeds
the staged reductions above, adds directed scoped assumptions, and is indexed
by source and remaining recursive observation depth. Its reflexive-transitive
closure, `GuardedSteps`, threads the remaining depth into the next step.
Environment-free computation preserves depth, while unfolding a validated
closure consumes one observation:

```text
Δprior(A) = S
-------------------------------- Delta
Δprior ; Δform ; Γ ⊢ₙ₊₁ A u ↦gₙ S u
```

An explicit `later` step may discard one observation without changing the
term. There is no same-depth recursive delta rule and no embedding of an
environment-dependent `Step` as a zero-cost guarded step.


### Self-indexed projectors

A family `T` may depend on the value `x` being checked. Its associated
self-indexed projector is the ordinary lambda term

```text
S = λx. T x
```

Consequently `S t ↦ T{x := t} t` is just beta reduction; there is no separate
self binder or self-instantiation rule in the core calculus. This shape is not
in itself recursive or inductive. It merely packages a value-indexed family as
a projector.

`Checks Δprior Δform Γ t A` is a proof-producing operational projector typing
judgment. Its soundness theorem yields equality generated by guarded
operational joinability at every finite recursive observation depth:

```text
Checks Δprior Δform Γ t A
  implies
∀n. Δprior ; Δform ; Γ ⊢ₙ A t ≃ t
```

`ContextEquiv` supplies symmetry, transitivity, congruence, and extensionality
over that joinability. Neither recursive idempotence nor star checking is a
primitive logical-equality rule: both first require directed reduction
certificates.

### Recursive blocks

A recursive block separates signatures from bodies. Checking omits every
signature implemented in the current phase, so a declaration cannot use its
own claimed type as evidence. Reduction may unfold only bodies validated by
earlier phases. Successful phases extend the environment for later ones.
Completion additionally requires every declared signature to be implemented
by some phase. Since phase checking looks up a signature for every body, a
complete block has neither orphan signatures nor undeclared bodies.

Recursion comes from closure names in the block: for example, the family in
the body of `Bool` refers to the closure name `Bool`. This is independent of
the lambda shape above. A self-indexed projector whose family mentions no
recursive closure is not thereby a recursive type.

Recursion is represented only by the environment equation `Δ(A) = S`; there
is no `μ` term. Operationally, the equation is exposed at an application head:

```text
A u ↦ Δ(A) u = S u
```

Recursive type formation uses guarded step-indexed operational induction. At
depth zero no recursive behavior is observable, so every directed step is
available. At a successor depth, recursive idempotence is itself a reduction:

```text
Δform(A) = S
ΓA = (* A ≃ A) :: (Idempotent A) :: Γ
Δprior ; Δform ; ΓA, x : A ⊢ₙ→ₘ S (A x) ↦g* S x
-------------------------------------------------- RecursiveIdempotence
Δprior ; Δform ; Γ ⊢ₙ₊₁→ₘ₊₁
  λy. A (A y) ↦g λy. A y
```

Here `↦g*` is directed `GuardedSteps`, not logical equality. The equations
`A : *`, `Idempotent A`, and `x : A` are directed assumptions at the predecessor
world and do not enter the surrounding context. There is no shape restriction
on `S`.

Guarded star checking preserves the source and remaining depths of its
operational certificate:

```text
Δprior ; Δform ; Γ ⊢ₙ→ₘ λy. A (A y) ↦g* λy. A y
------------------------------------------------ StarChecking
Δprior ; Δform ; Γ ⊢ₙ→ₘ * A ↦g A
```

Recursive idempotence therefore exists first as a directed reduction and only
then induces `* A ≃ A` through guarded joinability. The recursion depth remains
independent of the certification stage carried by embedded closed `Step`
derivations.

Ordinary computation in this judgment can unfold only `Δprior`, spending one
observation each time. It cannot use the provisional equation for `A` to turn
the guarded premise back into its conclusion. `Δform` is consulted only by
`RecursiveIdempotence`, which adds one observation to both ends of its body
certificate.

During a type phase, the phase bodies are installed in `Δform`, while
`Δprior` contains only earlier checked phases and all current-phase signature
equations remain excluded. Later phases may use earlier bodies through the
index-consuming delta rule. Individual phases are not exported as globally
validated environments.

Indexed environment satisfaction retains complete validation history:

```text
EnvironmentSatisfiesAt 0 Δ
EnvironmentSatisfiesAt n ∅

EnvironmentSatisfiesAt n Δprior
ChecksRecursiveBlock signatures Δprior phases Δresult
------------------------------------------------------ SealBlock
EnvironmentSatisfiesAt (n + 1) Δresult
```

`ValidatedEnv` packages a raw environment with satisfaction at every finite
depth. It starts from the empty environment and can be extended only by sealing
a complete, signature-covered block. Bool and Nat expose `validatedEnv` values
only after both phases succeed.

Finite legacy evaluation over a sealed environment is operationally adequate.
Every derivation has a finite unfolding cost `k` such that, for every base
depth `n`, it translates to:

```text
Δ ; Δ ; [] ⊢ₖ₊ₙ t ↦g*ₙ u
```

Delta contributes one to `k`; beta and starred idempotence contribute zero;
star checking recursively includes the cost of its certificate. Spending the
same budget on the other side, or truncating at world zero when the requested
world is shallower than `k`, proves `sealed_steps_equiv`: every finite `Steps`
derivation in a `ValidatedEnv` induces `ContextEquiv` at every observation
depth. This recovers unrestricted finite evaluation globally without a
same-world recursive delta rule.

The eta-recursive body `A = λx. A x` is guarded in this proof theory: at each
successor world its recursive use is interpreted at the predecessor world. It
may therefore denote an indefinitely delayed or bottom-like object. Guarded
idempotence establishes safety, not productivity; rejecting such declarations
would require an additional productivity or adequacy criterion.

For a previously available self-indexed projector `A = λx. T x`, constructor
checking preserves stable closure names. A body for `c : A` is checked against
`T{x := c}`, and a function returning `A` is checked pointwise under its domain
assumption. Thus indices remain `P true`, `P zero`, and `P (succ n)` rather than
being replaced by constructor implementation bodies.

Bool therefore uses:

```text
rec {
  Bool  : * =
    λb. (ΠP : Bool → *. P true → P false → P b) b

  true  : Bool =
    λP : Bool → *. λt : P true. λf : P false. t

  false : Bool =
    λP : Bool → *. λt : P true. λf : P false. f
}
```

Guarded induction validates the Bool closure in the type phase before its body
is exposed to constructor checks. Nat follows the same two-phase discipline.

Nat uses the full induction projector and supplies the induction hypothesis in
its successor implementation:

```text
rec {
  Nat  : * =
    λn. (ΠP : Nat → *.
      (Πk : Nat. P k → P (succ k)) → P zero → P n) n

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
- `Reduction.lean`: staged beta, closure application, and star reduction.
- `Confluence.lean`: joinability and conditional confluence infrastructure.
- `SelfTyping.lean`: directed guarded reduction, its generated projector
  equality, proof-producing contextual normalization, and all-depth typing
  soundness.
- `Recursive.lean`: recursive signatures, phased body validation, indexed
  environment satisfaction, sealing, and finite-cost operational adequacy.
- `BoolTest.lean` and `NatTest.lean`: annotated recursive declarations.
- `BoolCanonicity.lean`: regression proofs for the self-certifying Bool
  declaration that the phase realization context now excludes.

## Status

The Bool and Nat type phases, constructor phases, and complete recursive blocks
are proved without `sorry`. In particular, the validated declarations establish
`Bool : *`, `true : Bool`, `false : Bool`, `Nat : *`, `zero : Nat`, and
`succ : Nat → Nat`. The corresponding final theorems are
`BoolTest.block_valid` and `NatTest.block_valid`. These results use directed
guarded reductions for recursive idempotence and star checking. Internal
adequacy of sealed finite reduction is `sealed_steps_equiv`; adequacy with
respect to an external observational model, global normalization, productivity,
and unconditional confluence remain separate metatheoretic questions.

Recursive validation excludes every name implemented in the current phase.
This prevents a declaration such as `junk : Bool = junk` from certifying itself
with its own signature, and also blocks same-phase mutual self-certification.
`BoolCanonicity.junk_signature_excluded` proves that the exploit's crucial
equation is absent from the actual phase realization context. The former unsafe
derivation is no longer expressible because guarded equality cannot import
environment-dependent delta as a zero-cost legacy step. A full theorem that
every closed Bool inhabitant is equivalent to `true` or `false` remains to be
proved.

```sh
lake build
```