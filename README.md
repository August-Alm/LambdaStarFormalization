# LambdaStar

This project formalizes lambda-star with self types and finite recursive
definition environments in Lean 4.

```text
t, u ::= x | c | λx.t | ιx.T | (t u) | *
```

The operational rules include:

```text
(λx.t) u       ↦ [u/x]t
(ιx.T) t       ↦ ([t/x]T) t
c u            ↦ Δ(c) u
* A (* A t)    ↦ * A t
* A            ↦ A        when A has an earlier-stage idempotence certificate
```

Every body in `Δ` is closed, and each name has at most one body. Bare constants
remain stable closure identities; their bodies are exposed only at application
heads. Reduction is stratified so the premise of star checking is well-founded.

## Scoped Self Types

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

## Recursive Blocks

A recursive block separates signatures from bodies. Every signature is in
scope while checking a phase, but reduction may unfold only bodies validated
by earlier phases. Successful phases extend the environment for later ones.

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

## Status

The Bool and Nat type phases, constructor phases, and complete recursive blocks
are proved without `sorry`. In particular, the validated declarations establish
`Bool : *`, `true : Bool`, `false : Bool`, `Nat : *`, `zero : Nat`, and
`succ : Nat → Nat`. The successor implementation is the inductive Church term
`λn P s z. s n (n P s z)`.

The corresponding final theorems are `BoolTest.block_valid` and
`NatTest.block_valid`. These prove the scoped operational typing declarations;
global normalization, unconditional confluence, and datatype canonicity remain
separate metatheoretic questions.

```sh
lake build
```