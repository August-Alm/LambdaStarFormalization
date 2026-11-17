import FixedPoint.Reduction

namespace FixedPoint.Examples

open FixedPoint Term

/-- `λA : Any. λz : Any. A (A z)`. -/
def typeTerm : Term :=
  .lam .any (.lam .any (.app (.bvar 1) (.app (.bvar 1) (.bvar 0))))

/-- `λf : Any. λA : Type. λx : A. A (f A (A x))`. -/
def endTerm : Term :=
  .lam .any
    (.lam typeTerm
      (.lam (.bvar 0)
        (.app (.bvar 1)
          (.app (.app (.bvar 2) (.bvar 1))
            (.app (.bvar 1) (.bvar 0))))))

/-- `λA : Type. λx : A. x`. -/
def idTerm : Term :=
  .lam typeTerm (.lam (.bvar 0) (.bvar 0))

theorem id_membership_end : Membership (environment := .empty) [] idTerm endTerm := by
  refine ⟨1, .trans (.step (.beta (.step .any))) ?_⟩
  apply Equiv.lamBody
  apply Equiv.lamBody
  apply Equiv.trans
  · apply Equiv.app
    · exact .refl
    · apply Equiv.trans
      · apply Equiv.app
        · exact .step (.beta (.step (.assumption (by
            simp [Context.Lookup, Context.extend, typeTerm, idTerm,
              Term.substAt, Term.shift]))))
        · exact .refl
      · exact .step (.beta (.step (.appRight (.assumption (by
          simp [Context.Lookup, Context.extend, typeTerm, idTerm,
            Term.substAt, Term.shift])))))
  · apply Equiv.trans
    · exact .step (.appRight (.assumption (by
        simp [Context.Lookup, Context.extend, typeTerm, idTerm,
          Term.substAt, Term.shift])))
    · exact .step (.assumption (by
        simp [Context.Lookup, Context.extend, typeTerm, idTerm,
          Term.substAt, Term.shift]))

end FixedPoint.Examples
