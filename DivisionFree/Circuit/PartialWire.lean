import DivisionFree.Constants

/-! A wire that outputs zero where its selector is undefined. -/

namespace DivisionFree.Circuit

/-- Select an input coordinate when available and use zero otherwise. -/
def partialWire {I O : Type} [Fintype I] (select : O → Option I) :
    Circuit I O :=
  .comp (.pair (.wire id) (.zero : Circuit I PUnit))
    (.wire fun o => (select o).elim (Sum.inr PUnit.unit) Sum.inl)

@[simp] theorem partialWire_eval {R : Type*} [Ring R]
    {I O : Type} [Fintype I] (select : O → Option I)
    (input : I → R) (o : O) :
    (partialWire select).eval input o = (select o).elim 0 input := by
  cases h : select o <;> simp [partialWire, h]

@[simp] theorem partialWire_cost {I O : Type} [Fintype I]
    (select : O → Option I) : (partialWire select).cost = 0 := by
  simp [partialWire]

@[simp] theorem partialWire_multiplications {I O : Type} [Fintype I]
    (select : O → Option I) : (partialWire select).multiplications = 0 := by
  simp [partialWire]

@[simp] theorem partialWire_constantBits {I O : Type} [Fintype I]
    (select : O → Option I) : (partialWire select).constantBits = 0 := by
  simp [partialWire, Circuit.constantBits]

end DivisionFree.Circuit
