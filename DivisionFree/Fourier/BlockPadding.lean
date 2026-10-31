import DivisionFree.Fourier.BlockReductionCircuit

/-! Zero-pad a family of blocks and normalize by block subtraction. -/

namespace DivisionFree.Fourier

open DivisionFree

/-- Embed `p` blocks in `p+1` positions, filling the final block with zero. -/
def blockPadding (p m : ℕ) :
    Circuit (Fin p × Fin m) (Fin (p + 1) × Fin m) :=
  .comp
    (.bundle (fun ij : Fin (p + 1) × Fin m =>
      Fin.lastCases
        (.zero : Circuit (Fin p × Fin m) PUnit)
        (fun i => .wire (fun _ : PUnit => (i, ij.2))) ij.1))
    (.wire (fun ij : Fin (p + 1) × Fin m => (ij, PUnit.unit)))

@[simp] theorem blockPadding_eval_castSucc {R : Type*} [Ring R]
    (p m : ℕ) (x : Fin p × Fin m → R) (i : Fin p) (j : Fin m) :
    (blockPadding p m).eval x (i.castSucc, j) = x (i, j) := by
  simp [blockPadding]

@[simp] theorem blockPadding_eval_last {R : Type*} [Ring R]
    (p m : ℕ) (x : Fin p × Fin m → R) (j : Fin m) :
    (blockPadding p m).eval x (Fin.last p, j) = 0 := by
  simp [blockPadding]

theorem blockPadding_cost (p m : ℕ) : (blockPadding p m).cost = 0 := by
  classical
  simp only [blockPadding, Circuit.comp_cost, Circuit.bundle_cost, Circuit.wire_cost]
  apply Finset.sum_eq_zero
  intro ij hij
  refine Fin.lastCases ?_ (fun i => ?_) ij.1 <;> simp

theorem blockPadding_multiplications (p m : ℕ) :
    (blockPadding p m).multiplications = 0 := by
  classical
  simp only [blockPadding, Circuit.comp_multiplications,
    Circuit.bundle_multiplications, Circuit.wire_multiplications]
  apply Finset.sum_eq_zero
  intro ij hij
  refine Fin.lastCases ?_ (fun i => ?_) ij.1 <;> simp

theorem blockPadding_constantBits (p m : ℕ) :
    (blockPadding p m).constantBits = 0 := by
  classical
  simp only [blockPadding, Circuit.comp_constantBits, Circuit.constantBits]
  apply Finset.sum_eq_zero
  intro ij hij
  refine Fin.lastCases ?_ (fun i => ?_) ij.1 <;> simp [Circuit.constantBits]

/-- Reduce the final block by subtraction, then append a zero block. -/
def blockNormalize (p m : ℕ) :
    Circuit (Fin (p + 1) × Fin m) (Fin (p + 1) × Fin m) :=
  .comp (blockReduction p m) (blockPadding p m)

theorem blockNormalize_cost (p m : ℕ) :
    (blockNormalize p m).cost = 2 * p * m := by
  simp [blockNormalize, blockReduction_cost, blockPadding_cost]

@[simp] theorem blockNormalize_eval_last {R : Type*} [Ring R]
    (p m : ℕ) (x : Fin (p + 1) × Fin m → R) (j : Fin m) :
    (blockNormalize p m).eval x (Fin.last p, j) = 0 := by
  simp [blockNormalize]

@[simp] theorem blockNormalize_eval_castSucc {R : Type*} [Ring R]
    (p m : ℕ) (x : Fin (p + 1) × Fin m → R) (i : Fin p) (j : Fin m) :
    (blockNormalize p m).eval x (i.castSucc, j) =
      x (i.castSucc, j) - x (Fin.last p, j) := by
  simp [blockNormalize, blockReduction_eval]

end DivisionFree.Fourier
