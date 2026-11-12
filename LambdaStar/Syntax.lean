import Lean.Elab.Tactic.Omega

namespace LambdaStar

/-- Names referenced through a recursive definition environment. -/
abbrev Const := String

/-- Lambda-star terms, using de Bruijn indices for bound variables. -/
inductive Term where
  | bvar : Nat → Term
  | const : Const → Term
  | lam : Term → Term
  | iota : Term → Term
  | app : Term → Term → Term
  | star : Term
  deriving DecidableEq, Repr

namespace Term

/-- Raise every index `i ≥ cutoff` by `amount`. -/
def shift (amount cutoff : Nat) : Term → Term
  | bvar index =>
      if cutoff ≤ index then bvar (index + amount) else bvar index
  | const name => const name
  | lam body => lam (shift amount (cutoff + 1) body)
  | iota body => iota (shift amount (cutoff + 1) body)
  | app function argument =>
      app (shift amount cutoff function) (shift amount cutoff argument)
  | star => star

/-- `[A → B] = λf. λx. B (f (A x))`. -/
def arrow (domain codomain : Term) : Term :=
  .lam (.lam (.app (codomain.shift 2 0)
    (.app (.bvar 1) (.app (domain.shift 2 0) (.bvar 0)))))

/-- Shifting every eligible variable by zero leaves a term unchanged. -/
@[simp] theorem shift_zero (term : Term) (cutoff : Nat) :
    shift 0 cutoff term = term := by
  induction term generalizing cutoff with
  | bvar index => simp [shift]
  | const name => rfl
  | lam body inductionHypothesis => simp [shift, inductionHypothesis]
  | iota body inductionHypothesis => simp [shift, inductionHypothesis]
  | app function argument functionHypothesis argumentHypothesis =>
      simp [shift, functionHypothesis, argumentHypothesis]
  | star => rfl

/--
`substAt depth replacement body` implements capture-avoiding substitution
and removes the binder at `depth`:

    (λ. body) replacement  ↦β  substAt 0 replacement body.
-/
def substAt (depth : Nat) (replacement : Term) : Term → Term
  | bvar index =>
      if index = depth then
        shift depth 0 replacement
      else if depth < index then
        bvar (index - 1)
      else
        bvar index
  | const name => const name
  | lam body => lam (substAt (depth + 1) replacement body)
  | iota body => iota (substAt (depth + 1) replacement body)
  | app function argument =>
      app (substAt depth replacement function)
        (substAt depth replacement argument)
  | star => star

/-- Substitute an argument for the outermost bound variable. -/
def instantiate (body argument : Term) : Term :=
  substAt 0 argument body

/-- `WellScoped bound t` means every variable in `t` is bound below `bound`. -/
def WellScoped (bound : Nat) : Term → Prop
  | bvar index => index < bound
  | const _ => True
  | lam body => WellScoped (bound + 1) body
  | iota body => WellScoped (bound + 1) body
  | app function argument =>
      WellScoped bound function ∧ WellScoped bound argument
  | star => True

  instance wellScopedDecidable (bound : Nat) :
      (term : Term) → Decidable (WellScoped bound term)
    | .bvar index => inferInstanceAs (Decidable (index < bound))
    | .const _ => isTrue trivial
    | .lam body => wellScopedDecidable (bound + 1) body
    | iota body => wellScopedDecidable (bound + 1) body
    | .app function argument =>
        @instDecidableAnd (WellScoped bound function) (WellScoped bound argument)
          (wellScopedDecidable bound function) (wellScopedDecidable bound argument)
    | .star => isTrue trivial

/-- A closed term has no free de Bruijn indices: `FV(t) = ∅`. -/
abbrev Closed (term : Term) : Prop := WellScoped 0 term

/-- Increasing the ambient binder depth preserves well-scoping. -/
theorem WellScoped.mono (hScoped : WellScoped bound term)
    (hBound : bound ≤ larger) : WellScoped larger term := by
  induction term generalizing bound larger with
  | bvar index =>
      simp only [WellScoped] at hScoped ⊢
      omega
  | const name => trivial
  | lam body inductionHypothesis =>
      simp only [WellScoped] at hScoped ⊢
      exact inductionHypothesis hScoped (Nat.succ_le_succ hBound)
    | iota body inductionHypothesis =>
      simp only [WellScoped] at hScoped ⊢
      exact inductionHypothesis hScoped (Nat.succ_le_succ hBound)
  | app function argument functionHypothesis argumentHypothesis =>
      simp only [WellScoped] at hScoped ⊢
      exact ⟨functionHypothesis hScoped.1 hBound,
        argumentHypothesis hScoped.2 hBound⟩
  | star => trivial

/-- Substitution below all free indices is inert: `t[k := s] = t`. -/
theorem substAt_eq_self_of_wellScoped
    (hScoped : WellScoped depth term) : substAt depth replacement term = term := by
  induction term generalizing depth with
  | bvar index =>
      simp only [WellScoped] at hScoped
      simp [substAt, Nat.ne_of_lt hScoped, Nat.not_lt_of_ge (Nat.le_of_lt hScoped)]
  | const name => rfl
  | lam body inductionHypothesis =>
      simp only [WellScoped] at hScoped
      simp [substAt, inductionHypothesis hScoped]
    | iota body inductionHypothesis =>
      simp only [WellScoped] at hScoped
      simp [substAt, inductionHypothesis hScoped]
  | app function argument functionHypothesis argumentHypothesis =>
      simp only [WellScoped] at hScoped
      simp [substAt, functionHypothesis hScoped.1, argumentHypothesis hScoped.2]
  | star => rfl

/-- Successive shifts fuse when the second cutoff lies within the shifted range. -/
theorem shift_shift_of_le (term : Term) (left right inner outer : Nat)
    (hInner : inner ≤ outer) (hOuter : outer ≤ inner + left) :
    shift right outer (shift left inner term) = shift (left + right) inner term := by
  induction term generalizing left inner outer with
  | bvar index =>
      grind [shift]
  | const name => rfl
  | lam body inductionHypothesis =>
      have hOuter' : outer + 1 ≤ inner + 1 + left := by omega
      simp [shift, inductionHypothesis (left := left) (inner := inner + 1)
        (outer := outer + 1) (Nat.succ_le_succ hInner) hOuter']
  | iota body inductionHypothesis =>
      have hOuter' : outer + 1 ≤ inner + 1 + left := by omega
      simp [shift, inductionHypothesis (left := left) (inner := inner + 1)
        (outer := outer + 1) (Nat.succ_le_succ hInner) hOuter']
  | app function argument functionHypothesis argumentHypothesis =>
      simp [shift,
        functionHypothesis (left := left) (inner := inner) (outer := outer)
          hInner hOuter,
        argumentHypothesis (left := left) (inner := inner) (outer := outer)
          hInner hOuter]
  | star => rfl

/-- Two shifts commute when the outer cutoff accounts for the first shift. -/
theorem shift_shift_commute (term : Term) (left right base extra : Nat) :
    shift right (base + left + extra) (shift left base term) =
      shift left base (shift right (base + extra) term) := by
  induction term generalizing base with
  | bvar index => grind [shift]
  | const name => rfl
  | lam body inductionHypothesis =>
      simpa [shift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (base := base + 1)
  | iota body inductionHypothesis =>
      simpa [shift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (base := base + 1)
  | app function argument functionHypothesis argumentHypothesis =>
      simp [shift, functionHypothesis, argumentHypothesis]
  | star => rfl

/-- Shifting above a substitution depth commutes with substitution. -/
theorem shift_substAt (term replacement : Term) (amount depth extra : Nat) :
    shift amount (depth + extra) (substAt depth replacement term) =
      substAt depth (shift amount extra replacement)
        (shift amount (depth + extra + 1) term) := by
  induction term generalizing depth with
  | bvar index =>
      by_cases hIndex : index = depth
      · subst index
        simpa [substAt, shift, show ¬depth + extra + 1 ≤ depth by omega] using
          shift_shift_commute replacement depth amount 0 extra
      · grind [substAt, shift, shift_shift_of_le]
  | const name => rfl
  | lam body inductionHypothesis =>
      simpa [substAt, shift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (depth := depth + 1)
  | iota body inductionHypothesis =>
      simpa [substAt, shift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (depth := depth + 1)
  | app function argument functionHypothesis argumentHypothesis =>
      simp [substAt, shift, functionHypothesis, argumentHypothesis]
  | star => rfl

/-- Shifting commutes with capture-avoiding instantiation. -/
theorem shift_instantiate (body argument : Term) (amount cutoff : Nat) :
    shift amount cutoff (instantiate body argument) =
      instantiate (shift amount (cutoff + 1) body)
        (shift amount cutoff argument) := by
  simpa [instantiate] using
    shift_substAt body argument amount 0 cutoff

/-- Substitution commutes with a shift whose cutoff is below its target. -/
theorem substAt_shift_of_le (term replacement : Term) (amount depth cutoff : Nat)
    (hCutoff : cutoff ≤ depth) :
    substAt (depth + amount) replacement (shift amount cutoff term) =
      shift amount cutoff (substAt depth replacement term) := by
  induction term generalizing depth cutoff with
  | bvar index =>
      grind [shift, substAt, shift_shift_of_le]
  | const name => rfl
  | lam body inductionHypothesis =>
      simpa [shift, substAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (depth := depth + 1) (cutoff := cutoff + 1)
          (Nat.succ_le_succ hCutoff)
  | iota body inductionHypothesis =>
      simpa [shift, substAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (depth := depth + 1) (cutoff := cutoff + 1)
          (Nat.succ_le_succ hCutoff)
  | app function argument functionHypothesis argumentHypothesis =>
      simp [shift, substAt,
        functionHypothesis (depth := depth) (cutoff := cutoff) hCutoff,
        argumentHypothesis (depth := depth) (cutoff := cutoff) hCutoff]
  | star => rfl

/-- Removing an index inside a shifted range cancels one layer of that shift. -/
theorem substAt_shift_succ_of_le
  (term replacement : Term) (amount cutoff depth : Nat)
  (hCutoff : cutoff ≤ depth) (hDepth : depth ≤ cutoff + amount) :
  substAt depth replacement (shift (amount + 1) cutoff term) =
    shift amount cutoff term := by
  induction term generalizing cutoff depth with
  | bvar index =>
      grind [shift, substAt]
  | const name => rfl
  | lam body inductionHypothesis =>
    have hDepth' : depth + 1 ≤ cutoff + 1 + amount := by omega
    simp [shift, substAt,
    inductionHypothesis (cutoff := cutoff + 1) (depth := depth + 1)
      (Nat.succ_le_succ hCutoff) hDepth']
  | iota body inductionHypothesis =>
    have hDepth' : depth + 1 ≤ cutoff + 1 + amount := by omega
    simp [shift, substAt,
    inductionHypothesis (cutoff := cutoff + 1) (depth := depth + 1)
      (Nat.succ_le_succ hCutoff) hDepth']
  | app function argument functionHypothesis argumentHypothesis =>
    simp [shift, substAt,
    functionHypothesis (cutoff := cutoff) (depth := depth) hCutoff hDepth,
    argumentHypothesis (cutoff := cutoff) (depth := depth) hCutoff hDepth]
  | star => rfl

/-- Removing the fresh index cancels one layer from a shift. -/
theorem substAt_shift_succ (term replacement : Term) (amount depth : Nat) :
  substAt depth replacement (shift (amount + 1) depth term) =
    shift amount depth term := by
  apply substAt_shift_succ_of_le term replacement amount depth depth
  · exact Nat.le_refl depth
  · omega

/-- Substitution commutes with the shift that moves a term below `λ`. -/
theorem substAt_shift_one (term replacement : Term) (depth : Nat) :
    substAt (depth + 1) replacement (shift 1 0 term) =
      shift 1 0 (substAt depth replacement term) := by
  simpa using substAt_shift_of_le term replacement 1 depth 0 (Nat.zero_le depth)

/-- Opening with variable zero cancels the shift above its self binder. -/
theorem substAt_bvar_zero_shift_above (term : Term) (depth : Nat) :
    substAt depth (.bvar 0) (shift 1 (depth + 1) term) = term := by
  induction term generalizing depth with
  | bvar index => grind [shift, substAt]
  | const name => rfl
  | lam body inductionHypothesis =>
      simp [shift, substAt, inductionHypothesis]
    | iota body inductionHypothesis =>
      simp [shift, substAt, inductionHypothesis]
  | app function argument functionHypothesis argumentHypothesis =>
      simp [shift, substAt, functionHypothesis, argumentHypothesis]
  | star => rfl

  theorem substAt_bvar_shift_above (term : Term) (binders depth : Nat) :
    substAt depth (.bvar binders)
      (shift (binders + 1) (depth + 1) term) =
      shift binders depth term := by
    induction term generalizing binders depth with
    | bvar index => grind [shift, substAt]
    | const name => rfl
    | lam body inductionHypothesis =>
      simp [shift, substAt, inductionHypothesis]
    | iota body inductionHypothesis =>
      simp [shift, substAt, inductionHypothesis]
    | app function argument functionHypothesis argumentHypothesis =>
      simp [shift, substAt, functionHypothesis, argumentHypothesis]
    | star => rfl

@[simp] theorem instantiate_shift_above_self (body : Term) :
    instantiate (shift 1 1 body) (.bvar 0) = body := by
  simpa [instantiate] using substAt_bvar_zero_shift_above body 0

@[simp] theorem instantiate_shift_above_self_under
    (body : Term) (binders : Nat) :
    instantiate (shift (binders + 1) 1 body) (.bvar binders) =
      shift binders 0 body := by
  simpa [instantiate] using substAt_bvar_shift_above body binders 0

/-- Substituting through a β-contractum composes the two substitutions. -/
theorem substAt_substAt (body argument replacement : Term) (outer inner : Nat) :
    substAt (outer + inner) replacement (substAt inner argument body) =
      substAt inner (substAt outer replacement argument)
        (substAt (outer + inner + 1) replacement body) := by
  induction body generalizing outer inner with
  | bvar index =>
      by_cases hIndex : index = inner
      · subst index
        have hNe : inner ≠ outer + inner + 1 := by omega
        have hNotLt : ¬outer + inner + 1 < inner := by omega
        rw [show substAt inner argument (.bvar inner) = shift inner 0 argument by
          simp [substAt]]
        rw [substAt_shift_of_le argument replacement inner outer 0 (Nat.zero_le outer)]
        simp [substAt, hNe, hNotLt]
      · grind [substAt, substAt_shift_of_le, substAt_shift_succ_of_le]
  | const name => rfl
  | lam body inductionHypothesis =>
      simp [substAt, Nat.add_assoc, inductionHypothesis]
    | iota body inductionHypothesis =>
      simp [substAt, Nat.add_assoc, inductionHypothesis]
  | app function argument functionHypothesis argumentHypothesis =>
      simp [substAt, functionHypothesis, argumentHypothesis]
  | star => rfl

/-- Substituting through a β-contractum composes the two substitutions. -/
theorem substAt_instantiate (body argument replacement : Term) (depth : Nat) :
    substAt depth replacement (instantiate body argument) =
      instantiate (substAt (depth + 1) replacement body)
        (substAt depth replacement argument) := by
  simpa [instantiate] using substAt_substAt body argument replacement depth 0

end Term

/-- A deterministic environment of closed, possibly mutually recursive bodies. -/
structure DefEnv where
  defs : Const → Option Term
  closed : ∀ name body, defs name = some body → body.Closed

end LambdaStar
