import DivisionFree.Fourier.Basic
import DivisionFree.Polynomial.FullMultiplication

/-! Full polynomial products from zero-padded, unnormalized transforms.
The no-aliasing hypothesis bounds the entire product, not just its low half. -/

namespace DivisionFree.Fourier

open scoped BigOperators
open PolynomialArithmetic

variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R]

noncomputable def toPolynomial (a : ZMod n → R) : Polynomial R :=
  ∑ j : ZMod n, Polynomial.monomial j.val (a j)

@[simp] theorem toPolynomial_coeff (a : ZMod n → R) (k : ZMod n) :
    (toPolynomial a).coeff k.val = a k := by
  classical
  simp [toPolynomial, Polynomial.coeff_monomial, (ZMod.val_injective n).eq_iff]

theorem toPolynomial_coeff_zero (a : ZMod n → R) (k : ℕ) (hk : n ≤ k) :
    (toPolynomial a).coeff k = 0 := by
  classical
  simp only [toPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg]
  have hj := ZMod.val_lt j
  omega

theorem toPolynomial_coefficients (p : Polynomial R)
    (hp : ∀ k, n ≤ k → p.coeff k = 0) :
    toPolynomial (fun j : ZMod n => p.coeff j.val) = p := by
  apply Polynomial.ext
  intro k
  by_cases hk : k < n
  · have h := toPolynomial_coeff (fun j : ZMod n => p.coeff j.val) (k : ZMod n)
    simpa only [ZMod.val_natCast_of_lt hk] using h
  · rw [toPolynomial_coeff_zero _ k (by omega), hp k (by omega)]

theorem transform_eq_eval (χ : AddChar (ZMod n) R) (a : ZMod n → R) (k : ZMod n) :
    transform χ a k = (toPolynomial a).eval (χ k) := by
  classical
  simp only [transform, toPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have h := χ.map_nsmul_eq_pow j.val k
  simpa only [nsmul_eq_mul, ZMod.natCast_zmod_val] using h

theorem transform_coefficients (χ : AddChar (ZMod n) R) (p : Polynomial R)
    (hp : ∀ k, n ≤ k → p.coeff k = 0) (k : ZMod n) :
    transform χ (fun j : ZMod n => p.coeff j.val) k = p.eval (χ k) := by
  rw [transform_eq_eval, toPolynomial_coefficients p hp]

/-- A transform long enough to contain the full product has no cyclic aliasing. -/
theorem scaled_polynomial_product (χ : AddChar (ZMod n) R) (hχ : Orthogonal χ)
    (p q : Polynomial R)
    (hp : ∀ k, n ≤ k → p.coeff k = 0)
    (hq : ∀ k, n ≤ k → q.coeff k = 0)
    (hpq : ∀ k, n ≤ k → (p * q).coeff k = 0) (k : ZMod n) :
    inverseTransform χ
      (fun j => transform χ (fun i : ZMod n => p.coeff i.val) j *
        transform χ (fun i : ZMod n => q.coeff i.val) j) k =
      (n : R) * (p * q).coeff k.val := by
  have h : (fun j => transform χ (fun i : ZMod n => p.coeff i.val) j *
      transform χ (fun i : ZMod n => q.coeff i.val) j) =
      transform χ (fun i : ZMod n => (p * q).coeff i.val) := by
    funext j
    rw [transform_coefficients χ p hp, transform_coefficients χ q hq,
      transform_coefficients χ (p * q) hpq, Polynomial.eval_mul]
  rw [h, inverseTransform_transform χ hχ]

/-- Full multiplication of two length-`s` vectors, with zero padding to a
transform length at least `2*s`. The result includes every product coefficient. -/
theorem scaled_vector_product (χ : AddChar (ZMod n) R) (hχ : Orthogonal χ)
    (s : ℕ) (hs : 2 * s ≤ n) (a b : Fin s → R) (k : ZMod n) :
    inverseTransform χ
      (fun j => transform χ (fun i : ZMod n => (vectorPolynomial s a).coeff i.val) j *
        transform χ (fun i : ZMod n => (vectorPolynomial s b).coeff i.val) j) k =
      (n : R) * (vectorPolynomial s a * vectorPolynomial s b).coeff k.val := by
  apply scaled_polynomial_product χ hχ
  · intro l hl
    exact vectorPolynomial_coeff_eq_zero_of_ge s l a (by omega)
  · intro l hl
    exact vectorPolynomial_coeff_eq_zero_of_ge s l b (by omega)
  · intro l hl
    exact vectorPolynomial_mul_coeff_eq_zero_of_ge s l a b (by omega)

/-- Coefficient form of scaled cyclic convolution under the no-aliasing bounds.
No cancellation of the transform length is needed. -/
theorem scaled_convolution_coefficients (χ : AddChar (ZMod n) R)
    (hχ : Orthogonal χ) (p q : Polynomial R)
    (hp : ∀ k, n ≤ k → p.coeff k = 0)
    (hq : ∀ k, n ≤ k → q.coeff k = 0)
    (hpq : ∀ k, n ≤ k → (p * q).coeff k = 0) (k : ZMod n) :
    (n : R) * convolution (fun i : ZMod n => p.coeff i.val)
      (fun i : ZMod n => q.coeff i.val) k =
      (n : R) * (p * q).coeff k.val := by
  calc
    (n : R) * convolution (fun i : ZMod n => p.coeff i.val)
        (fun i : ZMod n => q.coeff i.val) k =
      inverseTransform χ
        (fun j => transform χ (fun i : ZMod n => p.coeff i.val) j *
          transform χ (fun i : ZMod n => q.coeff i.val) j) k :=
            (scaled_convolution χ hχ _ _ _).symm
    _ = (n : R) * (p * q).coeff k.val :=
      scaled_polynomial_product χ hχ p q hp hq hpq k

end DivisionFree.Fourier
