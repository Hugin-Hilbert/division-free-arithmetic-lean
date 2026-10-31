import DivisionFree.Fourier.CyclicFullProduct
import DivisionFree.Fourier.CyclotomicNormalization
import DivisionFree.Fourier.PrimePowerResources
import DivisionFree.Fourier.PrimePowerPadding
import DivisionFree.Polynomial.ScaledMultiplication

/-! Full ordinary polynomial products from the closed prime-power circuits.
The normalization recovers every coefficient, including the high half. -/

namespace DivisionFree.PolynomialArithmetic

open Fourier

universe u

/-- A complete multiplier scaled by a power of the chosen prime. -/
noncomputable def primePowerFullMultiplier (p n : ℕ) [NeZero p]
    (hp : p.Prime) (hn : 1 ≤ n) :
    ScaledFullMultiplier n ((p : ℤ) ^ primePowerScale (paddedExponent p n)) where
  circuit := cyclicFullProduct n (p ^ paddedExponent p n)
    (primePowerCircuit p (paddedExponent p n))
    (primeNormalize p (Nat.log p (2 * n) + 1) hp)
  correct := by
    intro R _ x
    by_cases hR : Nontrivial R
    · letI := hR
      have hlen : 2 * n ≤ (p - 1) * p ^ (Nat.log p (2 * n) + 1) := by
        simpa [paddedExponent] using paddedExponent_capacity hp.two_le hn
      have hD : (p - 1) * p ^ (Nat.log p (2 * n) + 1) ≤ p ^ paddedExponent p n := by
        change (p - 1) * p ^ (Nat.log p (2 * n) + 1) ≤ p ^ ((Nat.log p (2 * n) + 1) + 1)
        rw [pow_succ p (Nat.log p (2 * n) + 1)]
        simpa [Nat.mul_comm] using
          Nat.mul_le_mul_right (p ^ (Nat.log p (2 * n) + 1)) (Nat.sub_le p 1)
      have hdegree : (Polynomial.cyclotomic (p ^ paddedExponent p n) R).degree =
          (((p - 1) * p ^ (Nat.log p (2 * n) + 1) : ℕ) : WithBot ℕ) := by
        rw [Polynomial.degree_cyclotomic, Nat.totient_prime_pow hp
          (show 0 < paddedExponent p n by have := paddedExponent_ge_two p n; omega)]
        simp [paddedExponent, Nat.mul_comm]
      have h := cyclicFullProduct_correct n (p ^ paddedExponent p n)
        ((p - 1) * p ^ (Nat.log p (2 * n) + 1)) hlen hD hdegree
        (p ^ primePowerScale (paddedExponent p n))
        (primePowerCircuit p (paddedExponent p n))
        (primeNormalize p (Nat.log p (2 * n) + 1) hp)
        (primePowerCircuit_correct p hp (paddedExponent p n) R)
        (primeNormalize_correct p (Nat.log p (2 * n) + 1) hp)
        (primeNormalize_tail p (Nat.log p (2 * n) + 1) hp) x
      simpa only [Int.cast_pow, Int.cast_natCast, Nat.cast_pow] using h
    · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
      exact Subsingleton.elim _ _

theorem primePowerFullMultiplier_cost (p n : ℕ) [NeZero p]
    (hp : p.Prime) (hn : 1 ≤ n) :
    (primePowerFullMultiplier p n hp hn).circuit.cost =
      (primePowerCircuit p (paddedExponent p n)).cost +
        2 * (p - 1) * p ^ (Nat.log p (2 * n) + 1) := by
  simp only [primePowerFullMultiplier, cyclicFullProduct_cost]
  congr 1
  exact primeNormalize_cost p (Nat.log p (2 * n) + 1) hp

theorem primePowerFullMultiplier_constantBits (p n : ℕ) [NeZero p]
    (hp : p.Prime) (hn : 1 ≤ n) :
    (primePowerFullMultiplier p n hp hn).circuit.constantBits = 0 := by
  simp only [primePowerFullMultiplier, cyclicFullProduct, Circuit.comp_constantBits,
    cyclicInput_constantBits, primePowerCircuit_constantBits,
    Circuit.constantBits, Nat.add_zero, Nat.zero_add]
  exact primeNormalize_constantBits p (Nat.log p (2 * n) + 1) hp

/-- All ring operations, including input preparation and canonical extraction,
are included in this explicit quasi-linear bound. -/
theorem primePowerFullMultiplier_cost_le (p n : ℕ) [NeZero p]
    (hp : p.Prime) (hp3 : p ≤ 3) (hn : 1 ≤ n) :
    (primePowerFullMultiplier p n hp hn).circuit.cost ≤
      576 * n * (Nat.log 2 (2 * n) + 1) ^ 3 := by
  have hmain := primePowerCircuit_cost_le p hp.two_le hp3 (paddedExponent p n)
  have hsize := paddedExponent_total_length_small hp.two_le hp3 hn
  have hlog := paddedExponent_logBound hp.two_le hn
  have hpow : (max 1 (paddedExponent p n - 1)) ^ 3 ≤
      (Nat.log 2 (2 * n) + 1) ^ 3 := Nat.pow_le_pow_left hlog 3
  have hD : (p - 1) * p ^ (Nat.log p (2 * n) + 1) ≤ p ^ paddedExponent p n := by
    change (p - 1) * p ^ (Nat.log p (2 * n) + 1) ≤ p ^ ((Nat.log p (2 * n) + 1) + 1)
    rw [pow_succ p (Nat.log p (2 * n) + 1)]
    simpa [Nat.mul_comm] using
      Nat.mul_le_mul_right (p ^ (Nat.log p (2 * n) + 1)) (Nat.sub_le p 1)
  have hcubepos : 1 ≤ (Nat.log 2 (2 * n) + 1) ^ 3 := Nat.one_le_pow 3 _ (by omega)
  rw [primePowerFullMultiplier_cost]
  have hmain' : (primePowerCircuit p (paddedExponent p n)).cost ≤
      540 * n * (Nat.log 2 (2 * n) + 1) ^ 3 := by
    calc
      _ ≤ 30 * p ^ paddedExponent p n * (max 1 (paddedExponent p n - 1)) ^ 3 := hmain
      _ ≤ 30 * (18 * n) * (Nat.log 2 (2 * n) + 1) ^ 3 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 30 hsize) hpow
      _ = _ := by ring
  have hnorm : 2 * (p - 1) * p ^ (Nat.log p (2 * n) + 1) ≤ 36 * n := by
    nlinarith
  nlinarith

end DivisionFree.PolynomialArithmetic
