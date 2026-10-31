import DivisionFree.Fourier.BlockPadding
import DivisionFree.Fourier.Cyclotomic
import DivisionFree.Polynomial.Encoding

/-! Sparse reduction of a full cyclic representation to the prime-power
cyclotomic basis. The reduction circuit uses only coefficient subtractions. -/

namespace DivisionFree.Fourier

open scoped BigOperators
open PolynomialArithmetic

variable {R S : Type*} [CommRing R] [CommRing S]

noncomputable def blockEval {p m : ℕ} (f : R →+* S) (w : S)
    (x : Fin p × Fin m → R) : S :=
  ∑ i : Fin p, w ^ (m * i.val) * ∑ j : Fin m, f (x (i, j)) * w ^ j.val

theorem blockPadding_correct (p m : ℕ) (f : R →+* S) (w : S)
    (x : Fin p × Fin m → R) :
    blockEval f w ((blockPadding p m).eval x) = blockEval f w x := by
  unfold blockEval
  rw [Fin.sum_univ_castSucc]
  simp

theorem blockReduction_correct (p m : ℕ) (f : R →+* S) (w : S)
    (hw : ∑ i : Fin (p + 1), w ^ (m * i.val) = 0)
    (x : Fin (p + 1) × Fin m → R) :
    blockEval f w ((blockReduction p m).eval x) = blockEval f w x := by
  classical
  unfold blockEval
  simp only [blockReduction_eval, map_sub, sub_mul, Finset.sum_sub_distrib, mul_sub]
  rw [← Finset.sum_mul, Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc] at hw
  simp only [Fin.val_castSucc, Fin.val_last] at hw ⊢
  linear_combination -(∑ j : Fin m, f (x (Fin.last p, j)) * w ^ j.val) * hw

theorem blockNormalize_correct (p m : ℕ) (f : R →+* S) (w : S)
    (hw : ∑ i : Fin (p + 1), w ^ (m * i.val) = 0)
    (x : Fin (p + 1) × Fin m → R) :
    blockEval f w ((blockNormalize p m).eval x) = blockEval f w x := by
  have h : (blockNormalize p m).eval x =
      (blockPadding p m).eval ((blockReduction p m).eval x) := by
    funext j
    simp [blockNormalize]
  rw [h, blockPadding_correct, blockReduction_correct p m f w hw]

theorem blockEval_eq_polynomial {p m : ℕ} (f : R →+* S) (w : S)
    (x : Fin p × Fin m → R) :
    blockEval f w x =
      (vectorPolynomial (p * m) (fun i => x (finProdFinEquiv.symm i))).eval₂ f w := by
  classical
  simp only [vectorPolynomial, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial]
  rw [← finProdFinEquiv.sum_comp (fun i : Fin (p * m) =>
    f (x (finProdFinEquiv.symm i)) * w ^ i.val), Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, finProdFinEquiv_apply_val, blockEval,
    Finset.mul_sum, pow_add]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem cyclotomicRoot_geom_sum (p q : ℕ) (hp : p.Prime) :
    ∑ i : Fin p, cyclotomicRoot R (p ^ (q + 1)) ^ (p ^ q * i.val) = 0 := by
  have h := congrArg (AdjoinRoot.mk (Polynomial.cyclotomic (p ^ (q + 1)) R))
    (Polynomial.cyclotomic_prime_pow_eq_geom_sum (R := R) (n := q) hp)
  rw [AdjoinRoot.mk_self] at h
  rw [Fin.sum_univ_eq_sum_range
    (fun i => cyclotomicRoot R (p ^ (q + 1)) ^ (p ^ q * i)) p]
  simpa only [map_sum, map_pow, AdjoinRoot.mk_X, ← pow_mul,
    cyclotomicRoot] using h.symm

/-- Canonical sparse reduction inside the actual prime-power cyclotomic quotient.
The base ring remains arbitrary, including the zero ring. -/
theorem blockReduction_cyclotomic (p q : ℕ) (hp : (p + 1).Prime)
    (x : Fin (p + 1) × Fin ((p + 1) ^ q) → R) :
    blockEval (AdjoinRoot.of _) (cyclotomicRoot R ((p + 1) ^ (q + 1)))
        ((blockReduction p ((p + 1) ^ q)).eval x) =
      blockEval (AdjoinRoot.of _) (cyclotomicRoot R ((p + 1) ^ (q + 1))) x :=
  blockReduction_correct p ((p + 1) ^ q) _ _ (cyclotomicRoot_geom_sum (R := R) (p + 1) q hp) x

end DivisionFree.Fourier
