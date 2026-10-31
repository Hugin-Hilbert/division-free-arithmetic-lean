import DivisionFree.Fourier.BlockReduction
import DivisionFree.Fourier.FiniteTransform
import DivisionFree.Constants

/-! Normalize a cyclic coefficient family by block subtraction. -/

namespace DivisionFree.Fourier

open DivisionFree
open scoped BigOperators

private theorem cyclicTotal_ne_zero (p m : ℕ) [NeZero m] :
    (p + 1) * m ≠ 0 := by
  exact Nat.ne_of_gt (Nat.mul_pos (Nat.succ_pos p) (NeZero.pos m))

/-- View a cyclic coefficient vector as `(p+1)` consecutive blocks of width `m`.
-/
def cyclicBlocksEquiv (p m : ℕ) [NeZero m] :
    (Fin (p + 1) × Fin m) ≃ ZMod ((p + 1) * m) := by
  letI : NeZero ((p + 1) * m) := ⟨cyclicTotal_ne_zero p m⟩
  exact finProdFinEquiv.trans (cyclicIndexEquiv ((p + 1) * m))

/-- Normalize the cyclic vector by subtracting its final block from every earlier
block, then padding the final block with zero. -/
def cyclicNormalize (p m : ℕ) [NeZero m] :
    Circuit (ZMod ((p + 1) * m)) (ZMod ((p + 1) * m)) := by
  letI : NeZero ((p + 1) * m) := ⟨cyclicTotal_ne_zero p m⟩
  exact .comp
    (.comp
      (.wire (fun ij : Fin (p + 1) × Fin m => cyclicBlocksEquiv p m ij))
      (blockNormalize p m))
    (.wire (fun z : ZMod ((p + 1) * m) =>
      (cyclicBlocksEquiv p m).symm z))

theorem cyclicNormalize_cost (p m : ℕ) [NeZero m] :
    (cyclicNormalize p m).cost = 2 * p * m := by
  simp [cyclicNormalize, blockNormalize_cost]

theorem cyclicNormalize_multiplications (p m : ℕ) [NeZero m] :
    (cyclicNormalize p m).multiplications = 0 := by
  simp [cyclicNormalize, blockNormalize, blockReduction_multiplications,
    blockPadding_multiplications]

theorem cyclicNormalize_constantBits (p m : ℕ) [NeZero m] :
    (cyclicNormalize p m).constantBits = 0 := by
  simp [cyclicNormalize, blockNormalize, blockReduction_constantBits,
    blockPadding_constantBits, Circuit.constantBits]

private noncomputable def cyclicBlocks {R : Type*} (p m : ℕ) [NeZero m]
    (x : ZMod ((p + 1) * m) → R) : Fin (p + 1) × Fin m → R :=
  fun ij => x (cyclicBlocksEquiv p m ij)

@[simp] theorem cyclicNormalize_eval_blocks {R : Type*} [Ring R]
    (p m : ℕ) [NeZero m] (x : ZMod ((p + 1) * m) → R)
    (ij : Fin (p + 1) × Fin m) :
    (cyclicNormalize p m).eval x (cyclicBlocksEquiv p m ij) =
      (blockNormalize p m).eval (cyclicBlocks p m x) ij := by
  classical
  unfold cyclicNormalize
  simp only [Circuit.eval_comp, Circuit.eval_wire, Equiv.symm_apply_apply]
  rfl

@[simp] theorem cyclicNormalize_eval_last {R : Type*} [Ring R]
    (p m : ℕ) [NeZero m] (x : ZMod ((p + 1) * m) → R) (j : Fin m) :
    (cyclicNormalize p m).eval x
      (cyclicBlocksEquiv p m (Fin.last p, j)) = 0 := by
  rw [cyclicNormalize_eval_blocks]
  simp

@[simp] theorem cyclicNormalize_eval_castSucc {R : Type*} [Ring R]
    (p m : ℕ) [NeZero m] (x : ZMod ((p + 1) * m) → R)
    (i : Fin p) (j : Fin m) :
    (cyclicNormalize p m).eval x
      (cyclicBlocksEquiv p m (i.castSucc, j)) =
        x (cyclicBlocksEquiv p m (i.castSucc, j)) -
          x (cyclicBlocksEquiv p m (Fin.last p, j)) := by
  rw [cyclicNormalize_eval_blocks]
  simp [cyclicBlocks]

private theorem cyclicSum_eq_blockEval {R S : Type*} [CommRing R] [CommRing S]
    (p m : ℕ) [NeZero m] (f : R →+* S) (w : S)
    (x : ZMod ((p + 1) * m) → R) :
    (∑ z : ZMod ((p + 1) * m), f (x z) * w ^ z.val) =
      blockEval f w (cyclicBlocks p m x) := by
  classical
  letI : NeZero ((p + 1) * m) := ⟨cyclicTotal_ne_zero p m⟩
  rw [← (cyclicBlocksEquiv p m).sum_comp
    (fun z : ZMod ((p + 1) * m) => f (x z) * w ^ z.val)]
  simp only [cyclicBlocksEquiv, Equiv.trans_apply, finProdFinEquiv_apply_val,
    cyclicIndexEquiv_apply, cyclicBlocks, blockEval]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro i
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro j
  have hlt : j.val + m * i.val < (p + 1) * m := by
    nlinarith [i.isLt, j.isLt]
  simp only [ZMod.val_natCast_of_lt hlt, pow_add]
  ring

/-- The normalized cyclic representation has the same weighted coefficient sum
whenever the final block's geometric sum vanishes. -/
theorem cyclicNormalize_correct {R S : Type*} [CommRing R] [CommRing S]
    (p m : ℕ) [NeZero m] (f : R →+* S) (w : S)
    (hw : ∑ i : Fin (p + 1), w ^ (m * i.val) = 0)
    (x : ZMod ((p + 1) * m) → R) :
    (∑ z : ZMod ((p + 1) * m),
      f ((cyclicNormalize p m).eval x z) * w ^ z.val) =
    ∑ z : ZMod ((p + 1) * m), f (x z) * w ^ z.val := by
  calc
    (∑ z : ZMod ((p + 1) * m),
        f ((cyclicNormalize p m).eval x z) * w ^ z.val) =
        blockEval f w (cyclicBlocks p m ((cyclicNormalize p m).eval x)) :=
      cyclicSum_eq_blockEval p m f w ((cyclicNormalize p m).eval x)
    _ = blockEval f w (cyclicBlocks p m x) := by
      have heval : cyclicBlocks p m ((cyclicNormalize p m).eval x) =
          (blockNormalize p m).eval (cyclicBlocks p m x) := by
        funext ij
        exact cyclicNormalize_eval_blocks p m x ij
      rw [heval]
      exact blockNormalize_correct p m f w hw (cyclicBlocks p m x)
    _ = ∑ z : ZMod ((p + 1) * m), f (x z) * w ^ z.val :=
      (cyclicSum_eq_blockEval p m f w x).symm

end DivisionFree.Fourier
