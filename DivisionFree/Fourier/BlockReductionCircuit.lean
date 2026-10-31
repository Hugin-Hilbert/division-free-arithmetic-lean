import DivisionFree.Circuit
import DivisionFree.Constants

/-!
# Circuits for block reduction

The circuit subtracts the final block coefficientwise from each earlier block.
-/

namespace DivisionFree.Fourier

open DivisionFree

/-- Reduce `p+1` blocks to `p` blocks by subtracting the last block. -/
def blockReduction (p m : ℕ) :
    Circuit (Fin (p + 1) × Fin m) (Fin p × Fin m) :=
  .comp
    (.bundle (fun ij : Fin p × Fin m =>
      Circuit.sum
        (.wire (fun _ : PUnit => (ij.1.castSucc, ij.2)))
        (Circuit.negative (.wire (fun _ : PUnit => (Fin.last p, ij.2))))))
    (.wire (fun ij : Fin p × Fin m => (ij, PUnit.unit)))

@[simp] theorem blockReduction_eval {R : Type*} [Ring R]
    (p m : ℕ) (x : Fin (p + 1) × Fin m → R) (i : Fin p) (j : Fin m) :
    (blockReduction p m).eval x (i, j) =
      x (i.castSucc, j) - x (Fin.last p, j) := by
  simp [blockReduction, sub_eq_add_neg]

theorem blockReduction_cost (p m : ℕ) :
    (blockReduction p m).cost = 2 * p * m := by
  classical
  simp [blockReduction, mul_comm, mul_left_comm, mul_assoc]

theorem blockReduction_multiplications (p m : ℕ) :
    (blockReduction p m).multiplications = 0 := by
  classical
  simp [blockReduction]

theorem blockReduction_constantBits (p m : ℕ) :
    (blockReduction p m).constantBits = 0 := by
  classical
  simp [blockReduction, Circuit.constantBits, Circuit.sum, Circuit.negative]

end DivisionFree.Fourier
