# Recursive Bool

Bool and its constructors form one recursive declaration block:

```text
rec {
  Bool : * =
    λb. (ΠP : Bool → *.
      P true → P false → P b) b

  true : Bool =
    λP : Bool → *.
    λt : P true.
    λf : P false.
    t

  false : Bool =
    λP : Bool → *.
    λt : P true.
    λf : P false.
    f
}
```

The annotations on `true` and `false` are essential. They insert the
lambda-star projectors for the motive and branch proofs; the unannotated
Church terms are only readable erasures.

Validation is phased:

1. Validate the Bool projector at every observation depth with guarded
  recursive idempotence, producing a directed reduction certificate. Its body
  is available only through the provisional environment lookup from depth
  `n + 1` to `n`; ordinary computation sees the prior environment, and the
  Bool signature equation is absent.
2. Expose only the validated Bool body.
3. Validate each constructor body against the Bool family instantiated with its
  stable name: `T[true/b]` or `T[false/b]`.
4. Expose the complete environment only after both phases succeed and every
  signature has an implementation.

Bare closure names never unfold. Thus `true : Bool` cannot be established by
unfolding `true`, and the implementation lambda is never substituted for the
self index. The declarations and phase judgments are implemented in
`LambdaStar/BoolTest.lean`.