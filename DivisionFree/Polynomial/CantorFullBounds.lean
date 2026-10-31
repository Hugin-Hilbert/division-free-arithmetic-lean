import DivisionFree.Fourier.BinaryCantorResources
import DivisionFree.Fourier.CantorPadding
import DivisionFree.Fourier.TernaryMultiplier
import DivisionFree.Polynomial.PrimePowerFullMultiplication
import DivisionFree.Polynomial.TernaryFullMultiplication
import DivisionFree.Polynomial.FullProductResources

/-! Closed resource bounds for the concrete binary and ternary Cantor branches. -/

namespace DivisionFree.Fourier

theorem binaryCantorCircuit_cost_le (Q : ℕ) :
    (binaryCantorCircuit Q).cost ≤
      12 * 2 ^ Q * 2 ^ depth Q * (depth Q + 1) := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
      by_cases hsmall : Q ≤ 2
      · have hc := binaryCantorCircuit_base_cost_tight Q hsmall
        have hd : depth Q = 0 := by simp [depth, Nat.sub_eq_zero_of_le hsmall]
        rw [hd]
        simp only [pow_zero, Nat.mul_one, zero_add]
        omega
      · by_cases heq : Q = 3
        · subst Q
          have hc := binaryCantorCircuit_base_cost_tight 2 (by omega)
          have hs := binaryCantorCircuit_step_cost_tight 3 (by omega)
          have hs' : (binaryCantorCircuit 3).cost ≤
              4 * (binaryCantorCircuit 2).cost + 208 := by
            simpa [innerExponent, outerExponent] using hs
          norm_num [depth, Nat.size] at hc ⊢
          omega
        · have hQ : 3 < Q := by omega
          let q := innerExponent Q
          let r := outerExponent Q
          have hdepth : depth q + 1 = depth Q := depth_inner_succ Q (by omega)
          have hIH := ih q (innerExponent_lt Q (by omega))
          have hpowp : 2 ^ r * 2 ^ q = 2 ^ Q := by
            rw [← pow_add, Nat.add_comm r q, exponents_sum Q (by omega)]
          have hpow2 : 2 ^ depth q * 2 = 2 ^ depth Q := by
            rw [← hdepth, pow_succ]
          have hrec : 2 * 2 ^ r * (binaryCantorCircuit q).cost ≤
              12 * 2 ^ Q * 2 ^ depth Q * depth Q := by
            calc
              _ ≤ 2 * 2 ^ r * (12 * 2 ^ q * 2 ^ depth q * (depth q + 1)) :=
                Nat.mul_le_mul_left _ hIH
              _ = 12 * (2 ^ r * 2 ^ q) * (2 ^ depth q * 2) * (depth q + 1) := by ring
              _ = _ := by rw [hpowp, hpow2, hdepth]
          have htollbase : Q - 1 ≤ 2 ^ depth Q := by
            have ht := Nat.lt_size_self (Q - 2)
            dsimp [depth]
            omega
          have htoll := Nat.mul_le_mul_left (12 * 2 ^ Q) htollbase
          have hs := binaryCantorCircuit_step_cost_large Q hQ
          change (binaryCantorCircuit Q).cost ≤
            2 * 2 ^ r * (binaryCantorCircuit q).cost + 12 * 2 ^ Q * (Q - 1) at hs
          calc
            _ ≤ _ := hs
            _ ≤ 12 * 2 ^ Q * 2 ^ depth Q * depth Q + 12 * 2 ^ Q * 2 ^ depth Q :=
              Nat.add_le_add hrec htoll
            _ = _ := by ring

theorem binaryCantorCircuit_multiplications_le (Q : ℕ) :
    (binaryCantorCircuit Q).multiplications ≤
      4 * 2 ^ Q * 2 ^ depth Q := by
  apply cantorMultiplications_bound_general 4 2 (by omega) (by omega)
    (fun Q => (binaryCantorCircuit Q).multiplications)
  · intro Q hQ
    exact binaryCantorCircuit_base_multiplications_tight Q hQ
  · intro Q hQ
    rw [binaryCantorCircuit_step_multiplications Q hQ]

theorem ternaryCircuit_cost_le (Q : ℕ) :
    (ternaryCircuit Q).cost ≤
      18 * 3 ^ Q * 2 ^ depth Q * (depth Q + 1) := by
  apply cantorCost_bound 3 (by omega) (by omega) 18
    (fun Q => (ternaryCircuit Q).cost)
  · intro Q hQ
    exact ternaryCircuit_base_cost_le Q hQ
  · intro Q hQ
    exact ternaryCircuit_step_cost_le Q hQ

theorem ternaryCircuit_multiplications_le (Q : ℕ) :
    (ternaryCircuit Q).multiplications ≤
      9 * 3 ^ Q * 2 ^ depth Q := by
  apply cantorMultiplications_bound 3 (by omega) (by omega)
    (fun Q => (ternaryCircuit Q).multiplications)
  · intro Q hQ
    exact ternaryCircuit_base_multiplications_le Q hQ
  · intro Q hQ
    rw [ternaryCircuit_step_multiplications Q hQ]

end DivisionFree.Fourier

namespace DivisionFree.PolynomialArithmetic

open Fourier

theorem binaryFullMultiplier_cantor_cost_le (n : ℕ) (hn : 1 ≤ n) :
    (primePowerFullMultiplier 2 n Nat.prime_two hn).circuit.cost ≤
      208 * n * (Nat.log 2 (2 * n) + 1) *
        (Nat.size (Nat.log 2 (2 * n) + 1) + 1) := by
  rw [primePowerFullMultiplier_cost]
  exact cantorPaddedCost_le 2 n 12
    ((primePowerCircuit 2 (paddedExponent 2 n)).cost)
    (by omega) (by omega) hn (binaryCantorCircuit_cost_le _)

theorem binaryFullMultiplier_cantor_multiplications_le (n : ℕ) (hn : 1 ≤ n) :
    (primePowerFullMultiplier 2 n Nat.prime_two hn).circuit.multiplications ≤
      64 * n * (Nat.log 2 (2 * n) + 1) := by
  rw [primePowerFullMultiplier_multiplications]
  exact cantorPaddedMultiplications_general 2 n 4
    ((primePowerCircuit 2 (paddedExponent 2 n)).multiplications)
    (by omega) hn (binaryCantorCircuit_multiplications_le _)

theorem ternaryFullMultiplier_cantor_cost_le (n : ℕ) (hn : 1 ≤ n) :
    (ternaryFullMultiplier n hn).circuit.cost ≤
      684 * n * (Nat.log 2 (2 * n) + 1) *
        (Nat.size (Nat.log 2 (2 * n) + 1) + 1) := by
  rw [ternaryFullMultiplier_cost]
  exact cantorPaddedCost_le 3 n 18
    ((ternaryCircuit (paddedExponent 3 n)).cost)
    (by omega) (by omega) hn (ternaryCircuit_cost_le _)

theorem ternaryFullMultiplier_cantor_multiplications_le (n : ℕ) (hn : 1 ≤ n) :
    (ternaryFullMultiplier n hn).circuit.multiplications ≤
      324 * n * (Nat.log 2 (2 * n) + 1) := by
  rw [ternaryFullMultiplier_multiplications]
  exact cantorPaddedMultiplications_le 3 n
    ((ternaryCircuit (paddedExponent 3 n)).multiplications)
    (by omega) (by omega) hn (ternaryCircuit_multiplications_le _)

end DivisionFree.PolynomialArithmetic
