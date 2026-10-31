import DivisionFree.Fourier.CyclicTwist
import DivisionFree.Fourier.TwoBlockConvolution
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Full products from two cyclic transforms. The transform length is retained
throughout, so no nonzero or invertibility assumption on integers is needed. -/

namespace DivisionFree.Fourier

noncomputable section

theorem cyclicProduct_twoBlock_correct
    {M : ℕ} [NeZero M] {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (χ : AddChar (ZMod M) S)
    (s : ℕ) (hs : 0 < s) (r : ℕ) [NeZero (s ^ r)]
    (ψ : AddChar (ZMod (s ^ r)) S) (hψ : Orthogonal ψ)
    (e : ZMod M) (he : χ e = ψ 1) (d : S)
    (P : Circuit (Bool × ZMod M) (ZMod M))
    (hP : ∀ z : Bool × ZMod M → R,
      cyclicEval f χ (P.eval z) = d *
        (cyclicEval f χ (fun j => z (false, j)) *
          cyclicEval f χ (fun j => z (true, j))))
    (p q : Polynomial S)
    (hp : ∀ k, s ^ r ≤ k → p.coeff k = 0)
    (hq : ∀ k, s ^ r ≤ k → q.coeff k = 0)
    (hpq : ∀ k, 2 * s ^ r ≤ k → (p * q).coeff k = 0)
    (x : Bool × (Fin (s ^ r) × ZMod M) → R)
    (hx₀ : ∀ i : Fin (s ^ r),
      cyclicEval f χ (fun j => x (false, (i, j))) = p.coeff i.val)
    (hx₁ : ∀ i : Fin (s ^ r),
      cyclicEval f χ (fun j => x (true, (i, j))) = q.coeff i.val)
    (k : Fin (s ^ r)) :
    cyclicEval f χ (fun j =>
      (cyclicProduct M s hs r e P).eval x (k, j)) =
      d * ((s ^ r : ℕ) : S) *
        ((p * q).coeff k.val + (p * q).coeff (s ^ r + k.val)) := by
  rw [cyclicProduct_correct M f χ s hs r ψ hψ e he d P hP x k]
  have hA (i : ZMod (s ^ r)) :
      cyclicEval f χ (fun j => x (false, ((cyclicIndexEquiv (s ^ r)).symm i, j))) =
        p.coeff i.val := by
    simpa [cyclicIndexEquiv] using hx₀ ((cyclicIndexEquiv (s ^ r)).symm i)
  have hB (i : ZMod (s ^ r)) :
      cyclicEval f χ (fun j => x (true, ((cyclicIndexEquiv (s ^ r)).symm i, j))) =
        q.coeff i.val := by
    simpa [cyclicIndexEquiv] using hx₁ ((cyclicIndexEquiv (s ^ r)).symm i)
  simp_rw [hA, hB]
  rw [mul_assoc, scaled_convolution_twoBlock_coefficients ψ hψ p q hp hq hpq]
  have hkval : (cyclicIndexEquiv (s ^ r) k).val = k.val := by
    simp [cyclicIndexEquiv, ZMod.val_natCast_of_lt k.isLt]
  rw [hkval, mul_assoc]

theorem twistedCyclicProduct_twoBlock_correct
    {M : ℕ} [NeZero M] {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (χ : AddChar (ZMod M) S)
    (s : ℕ) (hs : 0 < s) (r : ℕ) [NeZero (s ^ r)]
    (ψ : AddChar (ZMod (s ^ r)) S) (hψ : Orthogonal ψ)
    (e t : ZMod M) (he : χ e = ψ 1) (d : S)
    (P : Circuit (Bool × ZMod M) (ZMod M))
    (hP : ∀ z : Bool × ZMod M → R,
      cyclicEval f χ (P.eval z) = d *
        (cyclicEval f χ (fun j => z (false, j)) *
          cyclicEval f χ (fun j => z (true, j))))
    (p q : Polynomial S)
    (hp : ∀ k, s ^ r ≤ k → p.coeff k = 0)
    (hq : ∀ k, s ^ r ≤ k → q.coeff k = 0)
    (hpq : ∀ k, 2 * s ^ r ≤ k → (p * q).coeff k = 0)
    (x : Bool × (Fin (s ^ r) × ZMod M) → R)
    (hx₀ : ∀ i : Fin (s ^ r),
      cyclicEval f χ (fun j => x (false, (i, j))) = p.coeff i.val)
    (hx₁ : ∀ i : Fin (s ^ r),
      cyclicEval f χ (fun j => x (true, (i, j))) = q.coeff i.val)
    (k : Fin (s ^ r)) :
    cyclicEval f χ (fun j =>
      (twistedCyclicProduct M s hs r e t P).eval x (k, j)) =
      d * ((s ^ r : ℕ) : S) *
        ((p * q).coeff k.val + χ t ^ (s ^ r) * (p * q).coeff (s ^ r + k.val)) := by
  let p' := p.comp (Polynomial.C (χ t) * Polynomial.X)
  let q' := q.comp (Polynomial.C (χ t) * Polynomial.X)
  have hp' (i : ℕ) (hi : s ^ r ≤ i) : p'.coeff i = 0 := by
    simp [p', Polynomial.comp_C_mul_X_coeff, hp i hi]
  have hq' (i : ℕ) (hi : s ^ r ≤ i) : q'.coeff i = 0 := by
    simp [q', Polynomial.comp_C_mul_X_coeff, hq i hi]
  have hpq' (i : ℕ) (hi : 2 * s ^ r ≤ i) : (p' * q').coeff i = 0 := by
    simp [p', q', ← Polynomial.mul_comp, Polynomial.comp_C_mul_X_coeff, hpq i hi]
  have htw₀ (i : Fin (s ^ r)) :
      cyclicEval f χ (fun j => (inputTwist M (s ^ r) t).eval x (false, (i, j))) =
        p'.coeff i.val := by
    rw [inputTwist_correct, hx₀]
    rw [show p' = p.comp (Polynomial.C (χ t) * Polynomial.X) from rfl,
      Polynomial.comp_C_mul_X_coeff, mul_comm]
  have htw₁ (i : Fin (s ^ r)) :
      cyclicEval f χ (fun j => (inputTwist M (s ^ r) t).eval x (true, (i, j))) =
        q'.coeff i.val := by
    rw [inputTwist_correct, hx₁]
    rw [show q' = q.comp (Polynomial.C (χ t) * Polynomial.X) from rfl,
      Polynomial.comp_C_mul_X_coeff, mul_comm]
  have hc := cyclicProduct_twoBlock_correct f χ s hs r ψ hψ e he d P hP
    p' q' hp' hq' hpq' ((inputTwist M (s ^ r) t).eval x) htw₀ htw₁ k
  have hunit : χ (-t) ^ k.val * χ t ^ k.val = 1 := by
    rw [← mul_pow, ← χ.map_add_eq_mul]
    simp
  have hpoly (i : ℕ) : (p' * q').coeff i = (p * q).coeff i * χ t ^ i := by
    simp [p', q', ← Polynomial.mul_comp]
  have hout : cyclicEval f χ (fun j =>
      (twistedCyclicProduct M s hs r e t P).eval x (k, j)) =
      χ (-t) ^ k.val * (d * ((s ^ r : ℕ) : S) *
        ((p' * q').coeff k.val + (p' * q').coeff (s ^ r + k.val))) := by
    simp only [twistedCyclicProduct, Circuit.eval_comp_function]
    rw [rowTwist_correct, hc]
  rw [hout, hpoly, hpoly, pow_add]
  calc
    χ (-t) ^ k.val * (d * ((s ^ r : ℕ) : S) *
        ((p * q).coeff k.val * χ t ^ k.val +
          (p * q).coeff (s ^ r + k.val) * (χ t ^ (s ^ r) * χ t ^ k.val))) =
        (χ (-t) ^ k.val * χ t ^ k.val) *
          (d * ((s ^ r : ℕ) : S) *
            ((p * q).coeff k.val + χ t ^ (s ^ r) * (p * q).coeff (s ^ r + k.val))) := by
      ring
    _ = _ := by rw [hunit, one_mul]

end
end DivisionFree.Fourier
