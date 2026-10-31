import DivisionFree.Fourier.TernaryMultiplier
import DivisionFree.Polynomial.FullProductResources

/-! Full ordinary products from the closed ternary cyclotomic circuit. -/

namespace DivisionFree.PolynomialArithmetic

open Fourier

universe u

private instance ternaryNonzero : NeZero 3 := ⟨by norm_num⟩

private theorem ternaryPrime : Nat.Prime 3 := by norm_num

/-- A full polynomial multiplier built from the recursive ternary circuit. -/
noncomputable def ternaryFullMultiplier (n : ℕ) (hn : 1 ≤ n) :
    ScaledFullMultiplier.{u} n ((3 : ℤ) ^ primePowerScale (paddedExponent 3 n)) := by
  refine ⟨cyclicFullProduct n (3 ^ paddedExponent 3 n)
    (ternaryCircuit (paddedExponent 3 n))
    (primeNormalize 3 (Nat.log 3 (2 * n) + 1) ternaryPrime), ?_⟩
  intro R _ x
  by_cases hR : Nontrivial R
  · letI := hR
    have hp : Nat.Prime 3 := ternaryPrime
    have hlen : 2 * n ≤ (3 - 1) * 3 ^ (Nat.log 3 (2 * n) + 1) := by
      simpa [paddedExponent] using paddedExponent_capacity (p := 3) (n := n) (by omega) hn
    have hD : (3 - 1) * 3 ^ (Nat.log 3 (2 * n) + 1) ≤ 3 ^ paddedExponent 3 n := by
      change (3 - 1) * 3 ^ (Nat.log 3 (2 * n) + 1) ≤
        3 ^ ((Nat.log 3 (2 * n) + 1) + 1)
      have hfac : 3 - 1 ≤ 3 := by omega
      calc
        (3 - 1) * 3 ^ (Nat.log 3 (2 * n) + 1) ≤
            3 * 3 ^ (Nat.log 3 (2 * n) + 1) :=
          Nat.mul_le_mul_right _ hfac
        _ = 3 ^ (Nat.log 3 (2 * n) + 1) * 3 := Nat.mul_comm _ _
        _ = 3 ^ ((Nat.log 3 (2 * n) + 1) + 1) := (pow_succ 3 (Nat.log 3 (2 * n) + 1)).symm
    have hdegree : (Polynomial.cyclotomic (3 ^ paddedExponent 3 n) R).degree =
        (((3 - 1) * 3 ^ (Nat.log 3 (2 * n) + 1) : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_cyclotomic, Nat.totient_prime_pow hp
        (show 0 < paddedExponent 3 n by have := paddedExponent_ge_two 3 n; omega)]
      simp [paddedExponent, Nat.mul_comm]
    have h := cyclicFullProduct_correct n (3 ^ paddedExponent 3 n)
      ((3 - 1) * 3 ^ (Nat.log 3 (2 * n) + 1)) hlen hD hdegree
      (3 ^ primePowerScale (paddedExponent 3 n))
      (ternaryCircuit (paddedExponent 3 n))
      (primeNormalize 3 (Nat.log 3 (2 * n) + 1) ternaryPrime)
      (ternaryCircuit_correct (paddedExponent 3 n) R)
      (primeNormalize_correct 3 (Nat.log 3 (2 * n) + 1) hp)
      (primeNormalize_tail 3 (Nat.log 3 (2 * n) + 1) hp) x
    simpa only [Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat] using h
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    exact Subsingleton.elim _ _

theorem ternaryFullMultiplier_cost (n : ℕ) (hn : 1 ≤ n) :
    (ternaryFullMultiplier.{u} n hn).circuit.cost =
      (ternaryCircuit (paddedExponent 3 n)).cost +
        4 * 3 ^ (Nat.log 3 (2 * n) + 1) := by
  change (cyclicFullProduct n (3 ^ paddedExponent 3 n)
    (ternaryCircuit (paddedExponent 3 n))
    (primeNormalize 3 (Nat.log 3 (2 * n) + 1) Nat.prime_three)).cost = _
  rw [cyclicFullProduct_cost]
  have h := primeNormalize_cost 3 (Nat.log 3 (2 * n) + 1) Nat.prime_three
  exact congrArg (fun c => (ternaryCircuit (paddedExponent 3 n)).cost + c) h

theorem ternaryFullMultiplier_multiplications (n : ℕ) (hn : 1 ≤ n) :
    (ternaryFullMultiplier.{u} n hn).circuit.multiplications =
      (ternaryCircuit (paddedExponent 3 n)).multiplications := by
  change (cyclicFullProduct n (3 ^ paddedExponent 3 n)
    (ternaryCircuit (paddedExponent 3 n))
    (primeNormalize 3 (Nat.log 3 (2 * n) + 1) Nat.prime_three)).multiplications = _
  rw [cyclicFullProduct_multiplications]
  have h := primeNormalize_multiplications 3 (Nat.log 3 (2 * n) + 1) Nat.prime_three
  exact (congrArg (fun c => (ternaryCircuit (paddedExponent 3 n)).multiplications + c) h).trans
    (Nat.add_zero _)

theorem ternaryFullMultiplier_constantBits (n : ℕ) (hn : 1 ≤ n) :
    (ternaryFullMultiplier.{u} n hn).circuit.constantBits = 0 := by
  simp only [ternaryFullMultiplier, cyclicFullProduct, Circuit.comp_constantBits,
    cyclicInput_constantBits, ternaryCircuit_constantBits, Circuit.constantBits,
    Nat.zero_add, Nat.add_zero]
  exact primeNormalize_constantBits 3 (Nat.log 3 (2 * n) + 1) Nat.prime_three

/-- The ternary full multiplier costs at most the prime-power construction for `3`. -/
theorem ternaryFullMultiplier_cost_le_old (n : ℕ) (hn : 1 ≤ n) :
    (ternaryFullMultiplier.{u} n hn).circuit.cost ≤
      (primePowerFullMultiplier.{u} 3 n Nat.prime_three hn).circuit.cost := by
  rw [ternaryFullMultiplier_cost, primePowerFullMultiplier_cost]
  exact Nat.add_le_add_right (ternaryCircuit_cost_le_old _) _

/-- The ternary full-product wrapper inherits the explicit padded-length bound. -/
theorem ternaryFullMultiplier_cost_le (n : ℕ) (hn : 1 ≤ n) :
    (ternaryFullMultiplier.{u} n hn).circuit.cost ≤
      576 * n * (Nat.log 2 (2 * n) + 1) ^ 3 := by
  exact (ternaryFullMultiplier_cost_le_old.{u} n hn).trans
    (primePowerFullMultiplier_cost_le.{u} 3 n Nat.prime_three (by decide) hn)

end DivisionFree.PolynomialArithmetic
