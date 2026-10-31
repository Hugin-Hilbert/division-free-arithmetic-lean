import DivisionFree.Fourier.TernaryProduct
import DivisionFree.Fourier.TernaryRoots
import DivisionFree.Fourier.CyclotomicMultiplier

/-! The ternary recursive extension step uses exactly two pointwise products
per outer coefficient. All coefficient recombination is explicitly charged. -/

namespace DivisionFree.Fourier

open scoped BigOperators
open PolynomialArithmetic
noncomputable section

universe u

variable (M : ℕ) [NeZero M]

def ternaryExtensionProduct (r : ℕ) (t : ZMod M)
    (P : Circuit (Bool × ZMod M) (ZMod M)) :
    Circuit (Bool × ZMod (M * 3 ^ r)) (ZMod (M * 3 ^ r)) :=
  .comp (splitInput M (3 ^ r) (3 ^ r))
    (.comp (ternaryProduct M r ((M / 3 ^ r : ℕ) : ZMod M) t P)
      (coefficientRecombine M (3 ^ r) (2 * 3 ^ r)))

theorem ternaryExtensionProduct_cost (r : ℕ) (t : ZMod M)
    (P : Circuit (Bool × ZMod M) (ZMod M)) :
    (ternaryExtensionProduct M r t P).cost =
      18 * M * r * 3 ^ r + 2 * 3 ^ r * P.cost + 10 * M * 3 ^ r := by
  simp [ternaryExtensionProduct, splitInput_cost, ternaryProduct_cost,
    coefficientRecombine_cost]
  ring

theorem ternaryExtensionProduct_multiplications (r : ℕ) (t : ZMod M)
    (P : Circuit (Bool × ZMod M) (ZMod M)) :
    (ternaryExtensionProduct M r t P).multiplications = 2 * 3 ^ r * P.multiplications := by
  simp [ternaryExtensionProduct, splitInput_multiplications,
    ternaryProduct_multiplications, coefficientRecombine_multiplications]

theorem ternaryExtensionProduct_constantBits (r : ℕ) (t : ZMod M)
    (P : Circuit (Bool × ZMod M) (ZMod M)) :
    (ternaryExtensionProduct M r t P).constantBits = 2 * 3 ^ r * P.constantBits := by
  simp [ternaryExtensionProduct, splitInput_constantBits,
    ternaryProduct_constantBits, coefficientRecombine_constantBits]

theorem ternaryExtensionProduct_correct {R T : Type*} [CommRing R] [CommRing T]
    (r : ℕ) (t : ZMod M) (hdiv : 3 ^ r ∣ M)
    (hζ : 1 + cyclotomicCharacter R M (3 ^ r • t) +
      cyclotomicCharacter R M (3 ^ r • t) ^ 2 = 0)
    (τ : CyclotomicRing R M →+* T) (f : R →+* T) (w : T)
    (hτ : ∀ a, τ (AdjoinRoot.of _ a) = f a)
    (hroot : τ (cyclotomicRoot R M) = w ^ (3 ^ r)) (hw : w ^ (M * 3 ^ r) = 1)
    (d : CyclotomicRing R M) (P : Circuit (Bool × ZMod M) (ZMod M))
    (hP : ∀ z : Bool × ZMod M → R, toCyclotomic (P.eval z) = d *
      (toCyclotomic (fun j => z (false, j)) * toCyclotomic (fun j => z (true, j))))
    (x : Bool × ZMod (M * 3 ^ r) → R) :
    (∑ j : ZMod (M * 3 ^ r), f ((ternaryExtensionProduct M r t P).eval x j) * w ^ j.val) =
      τ d * (3 ^ (r + 1) : ℕ) *
        ((∑ j : ZMod (M * 3 ^ r), f (x (false, j)) * w ^ j.val) *
          (∑ j : ZMod (M * 3 ^ r), f (x (true, j)) * w ^ j.val)) := by
  let A (b : Bool) := vectorPolynomial (3 ^ r) (fun k =>
    toCyclotomic (splitCoefficients M (3 ^ r) (fun j => x (b, j)) k))
  let y := (splitInput M (3 ^ r) (3 ^ r)).eval x
  let z := (ternaryProduct M r ((M / 3 ^ r : ℕ) : ZMod M) t P).eval y
  have hA (b : Bool) (k : ℕ) (hk : 3 ^ r ≤ k) : (A b).coeff k = 0 :=
    vectorPolynomial_coeff_eq_zero_of_ge (3 ^ r) k _ hk
  have hAB (k : ℕ) (hk : 2 * 3 ^ r ≤ k) : (A false * A true).coeff k = 0 :=
    vectorPolynomial_mul_coeff_eq_zero_of_ge (3 ^ r) k _ _ (by omega)
  have hy (b : Bool) (i : Fin (3 ^ r)) :
      toCyclotomic (fun j => y (b, (i, j))) = (A b).coeff i.val := by
    rw [show A b = vectorPolynomial (3 ^ r) (fun k =>
      toCyclotomic (splitCoefficients M (3 ^ r) (fun j => x (b, j)) k)) from rfl,
      vectorPolynomial_coeff_of_lt (3 ^ r) i.val _ i.isLt]
    congr 1
    funext j
    simp [y, splitInput_eval, i.isLt, splitCoefficients]
  have he : cyclotomicCharacter R M ((M / 3 ^ r : ℕ) : ZMod M) =
      cyclotomicSubcharacter R M (3 ^ r) hdiv 1 := by
    unfold cyclotomicCharacter cyclotomicSubcharacter
    rw [show (1 : ZMod (3 ^ r)) = ((1 : ℕ) : ZMod (3 ^ r)) by simp]
    rw [AddChar.zmodChar_apply', AddChar.zmodChar_apply', pow_one]
  have hz (k : Fin (2 * 3 ^ r)) : toCyclotomic (fun j => z (k, j)) =
      d * (3 ^ (r + 1) : ℕ) * (A false * A true).coeff k.val := by
    exact ternaryProduct_correct M (AdjoinRoot.of _) (cyclotomicCharacter R M) r
      (cyclotomicSubcharacter R M (3 ^ r) hdiv)
      (cyclotomicSubcharacter_orthogonal R M (3 ^ r) hdiv) _ t he hζ d P hP
      (A false) (A true) (hA false) (hA true) hAB y (hy false) (hy true) k
  have hzpoly : vectorPolynomial (2 * 3 ^ r) (fun k => toCyclotomic (fun j => z (k, j))) =
      Polynomial.C (d * (3 ^ (r + 1) : ℕ)) * (A false * A true) := by
    apply Polynomial.ext
    intro k
    by_cases hk : k < 2 * 3 ^ r
    · rw [vectorPolynomial_coeff_of_lt (2 * 3 ^ r) k _ hk, hz, Polynomial.coeff_C_mul]
    · rw [vectorPolynomial_coeff_eq_zero_of_ge (2 * 3 ^ r) k _ (by omega),
        Polynomial.coeff_C_mul, hAB k (by omega), mul_zero]
  have hAeval (b : Bool) : (A b).eval₂ τ w =
      ∑ j : ZMod (M * 3 ^ r), f (x (b, j)) * w ^ j.val := by
    rw [coefficientSum_split M (3 ^ r) f (fun j => x (b, j)) w]
    simp only [A, vectorPolynomial_eval₂, toCyclotomic_map_sum M (3 ^ r) τ f w hτ hroot]
  calc
    _ = ∑ k : Fin (2 * 3 ^ r),
        (∑ j : ZMod M, f (z (k, j)) * (w ^ (3 ^ r)) ^ j.val) * w ^ k.val := by
      have h := coefficientRecombine_transform M (3 ^ r) (2 * 3 ^ r) f w hw z
      simpa only [ternaryExtensionProduct, Circuit.eval_comp_function, z, y] using h
    _ = (vectorPolynomial (2 * 3 ^ r) (fun k => toCyclotomic (fun j => z (k, j)))).eval₂ τ w := by
      simp only [vectorPolynomial_eval₂, toCyclotomic_map_sum M (3 ^ r) τ f w hτ hroot]
    _ = _ := by
      rw [hzpoly, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_mul,
        hAeval false, hAeval true, map_mul, map_natCast]

omit [NeZero M] in
theorem ternaryExtensionProduct_primePower_correct (q r : ℕ)
    (hq : 0 < q) (hqr : r + 1 ≤ q)
    (d : ℕ) (P : Circuit (Bool × ZMod (3 ^ q)) (ZMod (3 ^ q)))
    (hP : CyclotomicCorrect.{u} (3 ^ q) d P) :
    CyclotomicCorrect.{u} (3 ^ q * 3 ^ r) (d * 3 ^ (r + 1))
      (ternaryExtensionProduct (3 ^ q) r
        (((3 ^ (q - (r + 1)) : ℕ)) : ZMod (3 ^ q)) P) := by
  intro R _ x
  have hζ : 1 + cyclotomicCharacter R (3 ^ q)
      (3 ^ r • ((3 ^ (q - (r + 1)) : ℕ) : ZMod (3 ^ q))) +
        cyclotomicCharacter R (3 ^ q)
          (3 ^ r • ((3 ^ (q - (r + 1)) : ℕ) : ZMod (3 ^ q))) ^ 2 = 0 := by
    rw [ternaryRootIndex_mul hqr]
    exact ternaryCyclotomicRoot_relation q hq
  have h := ternaryExtensionProduct_correct (3 ^ q) r
    (((3 ^ (q - (r + 1)) : ℕ)) : ZMod (3 ^ q))
    (Nat.pow_dvd_pow 3 (by omega)) hζ
    (cyclotomicSplitMap 3 q r Nat.prime_three hq) (AdjoinRoot.of _)
    (cyclotomicRoot R (3 ^ q * 3 ^ r))
    (cyclotomicSplitMap_of 3 q r Nat.prime_three hq)
    (cyclotomicSplitMap_root 3 q r Nat.prime_three hq)
    (cyclotomicRoot_pow R (3 ^ q * 3 ^ r)) (d : CyclotomicRing R (3 ^ q)) P (hP R) x
  simpa only [toCyclotomic, cyclicEval, cyclotomicCharacter, AddChar.zmodChar_apply,
    map_natCast, Nat.cast_mul, Nat.cast_pow] using h

end
end DivisionFree.Fourier
