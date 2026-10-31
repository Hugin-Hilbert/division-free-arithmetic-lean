import DivisionFree.Fourier.Polynomial
import DivisionFree.Fourier.TwoBlockEvaluation
import DivisionFree.Fourier.FiniteTransform

/-! Scaled cyclic convolution folded across two coefficient blocks. -/

namespace DivisionFree.Fourier

open scoped BigOperators
open PolynomialArithmetic

/-- Under a two-block support bound, scaled cyclic convolution recovers the
sum of the two product coefficients that fold to each cyclic index. -/
theorem scaled_convolution_twoBlock_coefficients {n : ℕ} [NeZero n]
    {R : Type*} [CommRing R] (χ : AddChar (ZMod n) R)
    (hχ : Orthogonal χ) (p q : Polynomial R)
    (hp : ∀ k, n ≤ k → p.coeff k = 0)
    (hq : ∀ k, n ≤ k → q.coeff k = 0)
    (hpq : ∀ k, 2 * n ≤ k → (p * q).coeff k = 0)
    (k : ZMod n) :
    (n : R) * convolution (fun j : ZMod n => p.coeff j.val)
        (fun j : ZMod n => q.coeff j.val) k =
      (n : R) * ((p * q).coeff k.val + (p * q).coeff (n + k.val)) := by
  classical
  let a : ZMod n → R := fun j => p.coeff j.val
  let b : ZMod n → R := fun j => q.coeff j.val
  let c : Polynomial R := p * q
  let d : ZMod n → R := fun j => c.coeff j.val + c.coeff (n + j.val)
  have hroot (t : ZMod n) : (χ t) ^ n = 1 := by
    have h := χ.map_nsmul_eq_pow n t
    simpa using h.symm
  have hfold (t : ZMod n) : transform χ d t = c.eval (χ t) := by
    have hblock := eval_twoBlock_coefficients n c hpq (χ t) 1 (hroot t)
    unfold transform
    calc
      (∑ j : ZMod n, d j * χ (j * t)) =
          ∑ j : ZMod n, (c.coeff j.val + c.coeff (n + j.val)) * (χ t) ^ j.val := by
            apply Finset.sum_congr rfl
            intro j hj
            have hchar : χ (j * t) = (χ t) ^ j.val := by
              have h := χ.map_nsmul_eq_pow j.val t
              simpa only [nsmul_eq_mul, ZMod.natCast_zmod_val] using h
            simp [d, c, hchar]
      _ = c.eval (χ t) := by
          calc
            (∑ j : ZMod n,
                (c.coeff j.val + c.coeff (n + j.val)) * (χ t) ^ j.val) =
                ∑ i : Fin n,
                  (c.coeff (cyclicIndexEquiv n i).val +
                    c.coeff (n + (cyclicIndexEquiv n i).val)) *
                    (χ t) ^ (cyclicIndexEquiv n i).val := by
                      rw [← (cyclicIndexEquiv n).sum_comp
                        (fun j : ZMod n =>
                          (c.coeff j.val + c.coeff (n + j.val)) * (χ t) ^ j.val)]
            _ = c.eval (χ t) := by
              have hval (i : Fin n) : (cyclicIndexEquiv n i).val = i.val := by
                simpa [cyclicIndexEquiv_apply] using (ZMod.val_natCast_of_lt i.isLt)
              simpa only [hval, one_mul] using hblock.symm
  have hprod (t : ZMod n) : transform χ a t * transform χ b t = c.eval (χ t) := by
    rw [transform_coefficients χ p hp, transform_coefficients χ q hq,
      Polynomial.eval_mul]
  have htrans : transform χ (convolution a b) = transform χ d := by
    funext t
    rw [transform_convolution]
    rw [hprod, hfold]
  have hleft := inverseTransform_transform χ hχ (convolution a b) k
  have hright := inverseTransform_transform χ hχ d k
  calc
    (n : R) * convolution a b k =
        inverseTransform χ (transform χ (convolution a b)) k := hleft.symm
    _ = inverseTransform χ (transform χ d) k := by rw [htrans]
    _ = (n : R) * d k := hright
    _ = (n : R) * (c.coeff k.val + c.coeff (n + k.val)) := by rfl

end DivisionFree.Fourier
