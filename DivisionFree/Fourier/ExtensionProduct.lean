import DivisionFree.Fourier.CoefficientSplit
import DivisionFree.Fourier.CoefficientRecombine
import DivisionFree.Fourier.CyclicProductPolynomial
import DivisionFree.Polynomial.VectorEvaluation

/-! A charged recursive multiplication step between cyclotomic extensions.
The pointwise circuit is an explicit argument, for subsequent recursion. -/

namespace DivisionFree.Fourier

open scoped BigOperators
open PolynomialArithmetic

noncomputable section

variable (m n : ℕ) [NeZero m] [NeZero n]

/-- Regroup, multiply the full block polynomials by Fourier transforms, and
scatter the result back into the large coefficient array. -/
def extensionProduct (s : ℕ) (hs : 0 < s) (r : ℕ) [NeZero (s ^ r)]
    (P : Circuit (Bool × ZMod m) (ZMod m)) :
    Circuit (Bool × ZMod (m * n)) (ZMod (m * n)) :=
  .comp (splitInput m n (s ^ r))
    (.comp (cyclicProduct m s hs r ((m / s ^ r : ℕ) : ZMod m) P)
      (coefficientRecombine m n (s ^ r)))

theorem extensionProduct_cost (s : ℕ) (hs : 0 < s) (r : ℕ) [NeZero (s ^ r)]
    (P : Circuit (Bool × ZMod m) (ZMod m)) :
    (extensionProduct m n s hs r P).cost =
      3 * m * s * r * s ^ r + s ^ r * P.cost + s ^ r * m := by
  simp [extensionProduct, splitInput_cost, cyclicProduct_cost,
    coefficientRecombine_cost, Nat.add_assoc]

omit [NeZero n] in
theorem toCyclotomic_map_sum {R T : Type*} [CommRing R] [CommRing T]
    (τ : CyclotomicRing R m →+* T) (f : R →+* T) (w : T)
    (hτ : ∀ a, τ (AdjoinRoot.of _ a) = f a)
    (hroot : τ (cyclotomicRoot R m) = w ^ n) (x : ZMod m → R) :
    τ (toCyclotomic x) = ∑ j : ZMod m, f (x j) * (w ^ n) ^ j.val := by
  simp only [toCyclotomic, cyclicEval, cyclotomicCharacter, AddChar.zmodChar_apply,
    map_sum, map_mul, map_pow, hτ, hroot]

private theorem splitInput_coefficients {R : Type*} [CommRing R]
    (L : ℕ) (x : Bool × ZMod (m * n) → R) (b : Bool) (i : Fin L) :
    toCyclotomic (fun j => (splitInput m n L).eval x (b, (i, j))) =
      (vectorPolynomial n (fun k =>
        toCyclotomic (splitCoefficients m n (fun j => x (b, j)) k))).coeff i.val := by
  by_cases hi : i.val < n
  · rw [vectorPolynomial_coeff_of_lt n i.val _ hi]
    congr 1
    funext j
    simp [splitInput_eval, hi, splitCoefficients]
  · rw [vectorPolynomial_coeff_eq_zero_of_ge n i.val _ (by omega)]
    simp [splitInput_eval, hi, toCyclotomic]

/-- The step preserves multiplication under every compatible map to a larger
ring. The transform length scales the answer; it is never inverted. -/
theorem extensionProduct_correct {R T : Type*} [CommRing R] [CommRing T]
    (s : ℕ) (hs : 0 < s) (r : ℕ) [NeZero (s ^ r)]
    (hlen : 2 * n ≤ s ^ r) (hdiv : s ^ r ∣ m)
    (τ : CyclotomicRing R m →+* T) (f : R →+* T) (w : T)
    (hτ : ∀ a, τ (AdjoinRoot.of _ a) = f a)
    (hroot : τ (cyclotomicRoot R m) = w ^ n) (hw : w ^ (m * n) = 1)
    (d : CyclotomicRing R m) (P : Circuit (Bool × ZMod m) (ZMod m))
    (hP : ∀ z : Bool × ZMod m → R, toCyclotomic (P.eval z) = d *
      (toCyclotomic (fun j => z (false, j)) * toCyclotomic (fun j => z (true, j))))
    (x : Bool × ZMod (m * n) → R) :
    (∑ j : ZMod (m * n), f ((extensionProduct m n s hs r P).eval x j) * w ^ j.val) =
      τ d * (s ^ r : ℕ) *
        ((∑ j : ZMod (m * n), f (x (false, j)) * w ^ j.val) *
          (∑ j : ZMod (m * n), f (x (true, j)) * w ^ j.val)) := by
  let A (b : Bool) := vectorPolynomial n (fun k =>
    toCyclotomic (splitCoefficients m n (fun j => x (b, j)) k))
  let y := (splitInput m n (s ^ r)).eval x
  let z := (cyclicProduct m s hs r ((m / s ^ r : ℕ) : ZMod m) P).eval y
  have hA (b : Bool) (k : ℕ) (hk : s ^ r ≤ k) : (A b).coeff k = 0 :=
    vectorPolynomial_coeff_eq_zero_of_ge n k _ (by omega)
  have hAB (k : ℕ) (hk : s ^ r ≤ k) : (A false * A true).coeff k = 0 :=
    vectorPolynomial_mul_coeff_eq_zero_of_ge n k _ _ (by omega)
  have he : cyclotomicCharacter R m ((m / s ^ r : ℕ) : ZMod m) =
      cyclotomicSubcharacter R m (s ^ r) hdiv 1 := by
    unfold cyclotomicCharacter cyclotomicSubcharacter
    rw [show (1 : ZMod (s ^ r)) = ((1 : ℕ) : ZMod (s ^ r)) by simp]
    rw [AddChar.zmodChar_apply', AddChar.zmodChar_apply', pow_one]
  have hz (k : Fin (s ^ r)) : toCyclotomic (fun j => z (k, j)) =
      d * (s ^ r : ℕ) * (A false * A true).coeff k.val := by
    exact cyclicProduct_polynomial_correct (AdjoinRoot.of _) (cyclotomicCharacter R m)
      s hs r (cyclotomicSubcharacter R m (s ^ r) hdiv)
      (cyclotomicSubcharacter_orthogonal R m (s ^ r) hdiv) _ he d P hP
      (A false) (A true) (hA false) (hA true) hAB y
      (splitInput_coefficients m n (s ^ r) x false)
      (splitInput_coefficients m n (s ^ r) x true) k
  have hzpoly : vectorPolynomial (s ^ r) (fun k => toCyclotomic (fun j => z (k, j))) =
      Polynomial.C (d * (s ^ r : ℕ)) * (A false * A true) := by
    apply Polynomial.ext
    intro k
    by_cases hk : k < s ^ r
    · rw [vectorPolynomial_coeff_of_lt (s ^ r) k _ hk, hz, Polynomial.coeff_C_mul]
    · rw [vectorPolynomial_coeff_eq_zero_of_ge (s ^ r) k _ (by omega),
        Polynomial.coeff_C_mul, hAB k (by omega), mul_zero]
  have hAeval (b : Bool) : (A b).eval₂ τ w =
      ∑ j : ZMod (m * n), f (x (b, j)) * w ^ j.val := by
    rw [coefficientSum_split m n f (fun j => x (b, j)) w]
    simp only [A, vectorPolynomial_eval₂, toCyclotomic_map_sum m n τ f w hτ hroot]
  calc
    _ = ∑ k : Fin (s ^ r),
        (∑ j : ZMod m, f (z (k, j)) * (w ^ n) ^ j.val) * w ^ k.val := by
      have h := coefficientRecombine_transform m n (s ^ r) f w hw z
      simpa only [extensionProduct, Circuit.eval_comp, z, y] using h
    _ = (vectorPolynomial (s ^ r) (fun k => toCyclotomic (fun j => z (k, j)))).eval₂ τ w := by
      simp only [vectorPolynomial_eval₂, toCyclotomic_map_sum m n τ f w hτ hroot]
    _ = τ d * (s ^ r : ℕ) *
        ((∑ j : ZMod (m * n), f (x (false, j)) * w ^ j.val) *
          (∑ j : ZMod (m * n), f (x (true, j)) * w ^ j.val)) := by
      rw [hzpoly, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_mul,
        hAeval false, hAeval true, map_mul, map_natCast]

end
end DivisionFree.Fourier
