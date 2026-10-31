import DivisionFree.Constants

/-! A concrete circuit for pointwise multiplication of two indexed vectors. -/

namespace DivisionFree.Circuit

/-- Multiply corresponding coordinates of two input families. -/
def pointwiseMultiply {T : Type} [Fintype T] : Circuit (Bool × T) T :=
  .comp
    (.bundle fun t : T =>
      .comp (.wire fun b : Bool => (b, t)) .mul)
    (.wire fun t : T => (t, PUnit.unit))

@[simp] theorem pointwiseMultiply_eval {R : Type*} [Ring R]
    {T : Type} [Fintype T] (x : Bool × T → R) (t : T) :
    (pointwiseMultiply (T := T)).eval x t = x (false, t) * x (true, t) := by
  simp [pointwiseMultiply]

@[simp] theorem pointwiseMultiply_cost {T : Type} [Fintype T] :
    (pointwiseMultiply (T := T)).cost = Fintype.card T := by
  simp [pointwiseMultiply]

@[simp] theorem pointwiseMultiply_multiplications {T : Type} [Fintype T] :
    (pointwiseMultiply (T := T)).multiplications = Fintype.card T := by
  simp [pointwiseMultiply]

@[simp] theorem pointwiseMultiply_constantBits {T : Type} [Fintype T] :
    (pointwiseMultiply (T := T)).constantBits = 0 := by
  simp [pointwiseMultiply, Circuit.constantBits]

end DivisionFree.Circuit
