import DivisionFree.LinearStraightLine.Basic
import DivisionFree.Polynomial.Schoolbook

/-! Transpose a rectangular selection of registers, including repeated and
zero outputs. Repeated output contributions are explicitly added. -/

namespace DivisionFree.LinearStraightLine

open scoped BigOperators

variable {n m k : ℕ} {R : Type*} [CommRing R]

noncomputable def fiberCircuit (w : Fin m → Option (Fin n)) (i : Fin n) :
    Circuit (Fin k ⊕ Fin m) PUnit :=
  Circuit.sumList (((Finset.univ.filter (fun j => w j = some i)).toList).map
    (fun j => Circuit.wire (fun _ => Sum.inr j)))

theorem fiberCircuit_eval (w : Fin m → Option (Fin n)) (i : Fin n)
    (p : Fin k → R) (y : Fin m → R) :
    (fiberCircuit w i).eval (Sum.elim p y) PUnit.unit =
      ∑ j : Fin m, if w j = some i then y j else 0 := by
  simp [fiberCircuit, Circuit.sumList_eval, List.map_map, Function.comp_def, Finset.sum_filter]

theorem fiberCircuit_cost (w : Fin m → Option (Fin n)) (i : Fin n) :
    (fiberCircuit (k := k) w i).cost = (Finset.univ.filter (fun j => w j = some i)).card := by
  simp [fiberCircuit, Circuit.sumList_cost, List.map_map, Function.comp_def]

noncomputable def outputTranspose (w : Fin m → Option (Fin n)) :
    Circuit (Fin k ⊕ Fin m) (Fin n) :=
  .comp (.bundle (fiberCircuit w)) (.wire (fun i => (i, PUnit.unit)))

theorem outputTranspose_eval (w : Fin m → Option (Fin n))
    (p : Fin k → R) (y : Fin m → R) (i : Fin n) :
    (outputTranspose w).eval (Sum.elim p y) i =
      ∑ j : Fin m, if w j = some i then y j else 0 := by
  simp [outputTranspose, fiberCircuit_eval]

/-- At most one addition is charged per selected output. No cost depends on
the product of the input and output dimensions. -/
theorem outputTranspose_cost (w : Fin m → Option (Fin n)) :
    (outputTranspose (k := k) w).cost ≤ m := by
  simp only [outputTranspose, Circuit.comp_cost, Circuit.bundle_cost,
    Circuit.wire_cost, Nat.add_zero, fiberCircuit_cost]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    (∑ j : Fin m, ∑ i : Fin n, if w j = some i then (1 : ℕ) else 0) ≤
        ∑ _ : Fin m, 1 := by
      apply Finset.sum_le_sum
      intro j _
      cases w j <;> simp
    _ = m := by simp

theorem outputTranspose_adjoint (w : Fin m → Option (Fin n))
    (p : Fin k → R) (x : Fin n → R) (y : Fin m → R) :
    outputValue w x ⬝ᵥ y = x ⬝ᵥ (outputTranspose w).eval (Sum.elim p y) := by
  simp only [dotProduct, outputTranspose_eval, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  cases h : w j <;> simp [outputValue, h, mul_ite]

end DivisionFree.LinearStraightLine
