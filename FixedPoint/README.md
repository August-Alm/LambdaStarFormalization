# FixedPoint

t, u, A ::= x | λx:A.t | (t u) | Any

We write ↦ for one-step reduction, ↦* for its reflexive-transitive
closure, and ~ for the least compatible equivalence containing ↦ and
the eta equation below. A context Γ contains assumptions x:A. The
annotation A need not itself be a projector; x:A records the local
assumption that x is a fixed point of A. Contexts are considered modulo
conversion of their annotations.

Any well-scoped annotation may extend a context:

Γ context    FV(A) ⊆ dom(Γ)    x fresh
--------------------------------------
Γ, x:A context

A term inhabits an annotation exactly when it is a fixed point of that
annotation:

Γ ⊢ (A u) ~ u
-------------
Γ ⊢ u : A

The distinguished annotation `Any` is the identity projector:

----------------
Γ ⊢ (Any u) ↦ u

Eta conversion is restricted to `Any`-annotated lambdas. This removes
an extensionally redundant universal check without erasing a
meaningful domain annotation:

---------------------  [z fresh in t]
Γ ⊢ λz:any.(t z) ~ t

Define the classifier of honest types as the ordinary term

Type := λA:any.λz:any.(A (A z))

Then A inhabits Type exactly when A is a projector:

Γ ⊢ A : Type
iff  Γ ⊢ (Type A) ~ A
iff  Γ ⊢ λz:Any.(A (A z)) ~ λz:Any.(A z).

We may therefore use `Γ ⊢ A type` or `Γ ⊢ A projector` as shorthand
for `Γ ⊢ A : Type`. The classifier `Type` is not itself be a
projector. In particular, X:Type is a valid contextual assumption and
λX:Type.t expresses polymorphism over projector annotations without
requiring Type:Type.

A variable assumption supplies the corresponding fixed-point
contraction:

x:A ∈ Γ
-----------
Γ ⊢ (A x) ↦ x

Reduction is compatible with applications, lambda bodies, and lambda
annotations:

Γ ⊢ t ↦ t'
----------------
Γ ⊢ (t u) ↦ (t' u)

Γ ⊢ u ↦ u'
----------------
Γ ⊢ (t u) ↦ (t u')

Γ, x:A ⊢ t ↦ t'
-------------------------
Γ ⊢ λx:A.t ↦ λx:A.t'

Γ ⊢ A ↦ A'
-------------------------
Γ ⊢ λx:A.t ↦ λx:A'.t

Beta reduction checks the argument against the annotation:

Γ ⊢ u : A
------------------------------
Γ ⊢ ((λx:A.t) u) ↦ t{u/x}

The membership premise is intentionally conversion-based rather than
the one-step condition (A u) ↦ u. In particular, it is preserved when
A or u reduces. It also supplies exactly the evidence required by
substitution: replacing x:A by u turns the contextual contraction
(A x) ↦ x into the valid equation (A u) ~ u.

Membership, conversion, and conditional beta reduction are mutually
dependent. Their intended meaning is the least finitary closure; a
formalization can expose this using stages, with conditional beta at
stage n + 1 consuming membership evidence from stage n. Projectorhood
is derived from membership in Type rather than imposed on all context
annotations.

## Mutually recursive definitions

A recursive block consists of distinct names, each carrying both a closed
annotation and a closed body:

```text
rec {
	c₁ : A₁ = t₁
	...
	cₙ : Aₙ = tₙ
}
```

Validation partitions the supplied definitions into phases. Names are unique
and fresh in each phase. `ChecksImplementation` specializes how a body may
realize its annotation:

```text
direct:       Δprior; · ⊢ ti : Ai

formation:    Ai = Type
			  Δprior + (ci : Type = ti); · ⊢ ti : Type

named:        Ai = A
			  Δprior(A) = λx : Any.F
			  Δprior + (ci : A = ti); · ⊢ F{ci/x} ~ ti
```

The provisional formation environment contains only the declaration currently
being checked in addition to `Δprior`. Direct checks use only `Δprior`.
Recursive type formation is restricted to the distinguished `Type` annotation
and checks the actual body in the singleton formation environment. A named
check must find its projector/type body in `Δprior`, but
checks conversion in the singleton formation environment. This is guarded
singleton self-unfolding, not ordinary prior-only checking: the implementation
currently being checked may delta-unfold when applied, while sibling bodies and
the rest of the current phase remain unavailable. A validation history must
cover the original list of atomic signature/body definitions exactly once
before it produces a `ValidatedEnv`.

Recursive names remain stable when bare and unfold only when applied:

```text
c : A = t ∈ Δ
-----------------
Δ; Γ ⊢ (c u) ↦ (t u)
```

After validation, recursive induction exposes each declared name as a fixed
point of its annotation:

```text
c : A = t ∈ Δ
---------------
Δ; Γ ⊢ (A c) ↦ c
```

The public recursion helpers require a `ValidatedEnv`. The low-level reduction
relation retains the induction and applied-delta rules, so the calculus, stable
bare constants, and applied-only unfolding are unchanged. Recursive type
formation checks the proposed body itself in the singleton provisional
environment. Recursive induction certifies the stable provisional name, and
applied delta transfers the resulting projector equation to the body. Named
checks obtain their signature/type body from the prior environment and may
provisionally unfold only their own implementation when it is applied.

## TODO: Strong leftmost-outermost beta-eta normalization

1. Reduce the leftmost outermost redex.
2. Reduce under lambda annotations and bodies.
3. Orient the restricted eta equation as contraction:
```
λx:any.(t x) ↦η t    [x fresh in t]
```
4. For conditional beta, normalize the membership equation:
```
nfΓ(A u) = nfΓ(u)
--------------------------------
nfΓ(((λx:A.t) u)) = nfΓ(t{u/x})
```
5. Apply contextual contractions deterministically:
```
x:A ∈ Γ
-----------
(A x) ↦ x
```
If the combined beta, contextual, and eta reduction is confluent, then for
terms whose normalization terminates:
```
t ~ u implies nfΓ(t) = nfΓ(u) 
```
where equality (on the right) is syntactic equality modulo alpha-renaming.

## Implementation notes

`Syntax.lean` defines annotated de Bruijn terms, stable recursive constants,
capture-avoiding shifting and substitution, contexts, and unique recursive
environments with complete signature/body entries.

`Reduction.lean` defines `Step`, its equivalence closure `Equiv`, and the
membership judgment `Membership Γ term annotation`. A beta step at stage
`n + 1` is permitted only when its argument has the lambda annotation at stage
`n`. The `lift` constructors preserve established steps and equivalences at
higher stages; stages therefore measure certification depth, not evaluation
length.

`Examples.lean` gives closed encodings of `Type`, `End`, and polymorphic
identity. Its theorem `id_membership_end` proves `Membership [] idTerm endTerm`
at stage 1 using only `Any`, scoped assumptions, beta, congruence, and the
equivalence rules.

`Recursive.lean` defines `ChecksImplementation`,
`RecursivePhaseValidation`, `ValidationHistory`, and `ValidatedEnv`. Recursive
type formation uses a singleton provisional environment, direct checks use
only the prior environment, and named checks look up their type body in the
prior environment while checking conversion with guarded singleton
self-unfolding. No check can observe a sibling body. Its recursive-induction
and applied-unfolding helpers consume a validated environment, and it proves
that bare recursive names cannot reduce.

`Bool.lean` divides `Bool` and `true`/`false` into two phases. Sealing is exposed
by unconditional `sealEnvironment` and `validatedEnv`. The theorems
`true_has_type` and `false_has_type` validate the exact constructor bodies:
each obtains the Bool family from the earlier phase and, in its own singleton
formation environment, delta-unfolds only its applied constructor. It then
uses conditional beta justified by the scoped predicate and branch assumptions
and finishes by congruence and contextual contraction. Consequently
`true_membership_bool`, `false_membership_bool`, and
`bool_unfolds_when_applied` are unconditional.

`bool_has_type` validates `boolBody : Type` in the singleton provisional
environment. It derives projectorhood of stable `Bool` from recursive
induction, applies that equality pointwise, and uses applied delta in both
directions to transfer idempotence to `boolBody`. Thus all three supplied
bodies, `boolBody`, `trueBody`, and `falseBody`, are genuinely checked before
the environment is sealed.