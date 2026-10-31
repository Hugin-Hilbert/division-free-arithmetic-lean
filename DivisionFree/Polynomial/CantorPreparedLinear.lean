import DivisionFree.Circuit.Bihomogeneous
import DivisionFree.Polynomial.PreparedLinear
import DivisionFree.Polynomial.CantorMultiplication
import DivisionFree.Polynomial.FastMultiplication

/-! Cantor--Kaltofen bounds for the prepared linearization of the actual
public full multiplier. -/

namespace DivisionFree.PolynomialArithmetic

open DivisionFree
open DivisionFree.Circuit

universe u

private theorem vectorPolynomial_scale {R : Type*} [CommRing R]
    (k : ℕ) (r : R) (x : Fin k → R) :
    vectorPolynomial k (fun i => r * x i) = Polynomial.C r * vectorPolynomial k x := by
  classical
  apply Polynomial.ext
  intro i
  by_cases hi : i < k
  · rw [vectorPolynomial_coeff_of_lt k i _ hi,
      Polynomial.coeff_C_mul, vectorPolynomial_coeff_of_lt k i x hi]
  · have hki : k ≤ i := Nat.le_of_not_gt hi
    rw [vectorPolynomial_coeff_eq_zero_of_ge k i _ hki,
      Polynomial.coeff_C_mul, vectorPolynomial_coeff_eq_zero_of_ge k i x hki]
    simp

theorem fastFullMultiplier_splitCircuit_bihomogeneous (n : ℕ) :
    Circuit.Bihomogeneous.{u} (fastFullMultiplier.{u} n).splitCircuit := by
  intro R _ a b s t
  apply vectorPolynomial_injective (2 * n)
  calc
    vectorPolynomial (2 * n)
        ((fastFullMultiplier.{u} n).splitCircuit.eval
          (Sum.elim (fun i => s * a i) (fun i => t * b i))) =
        vectorPolynomial n (fun i => s * a i) *
          vectorPolynomial n (fun i => t * b i) := by
            rw [(fastFullMultiplier.{u} n).splitCircuit_eval]
            exact (fastFullMultiplier.{u} n).correct R
              (fun z : Bool × Fin n => if z.1 then t * b z.2 else s * a z.2)
    _ = Polynomial.C (s * t) *
          (vectorPolynomial n a * vectorPolynomial n b) := by
            rw [vectorPolynomial_scale, vectorPolynomial_scale]
            rw [map_mul (Polynomial.C : R →+* Polynomial R) s t]
            ring
    _ = Polynomial.C (s * t) *
          vectorPolynomial (2 * n)
            ((fastFullMultiplier.{u} n).splitCircuit.eval (Sum.elim a b)) := by
            rw [(fastFullMultiplier.{u} n).splitCircuit_eval]
            rw [(fastFullMultiplier.{u} n).correct R
              (fun z : Bool × Fin n => if z.1 then b z.2 else a z.2)]
            simp
    _ = vectorPolynomial (2 * n)
          (fun i => s * t *
            (fastFullMultiplier.{u} n).splitCircuit.eval (Sum.elim a b) i) := by
            rw [vectorPolynomial_scale]

/-- The second logarithmic factor is at least three whenever the input
length contributes a nonzero cost. -/
theorem cantor_log_scale_three (n : ℕ) :
    3 * (n * (Nat.log 2 (2 * n) + 1)) ≤
      (n * (Nat.log 2 (2 * n) + 1)) *
        (Nat.log 2 (Nat.log 2 (2 * n) + 1) + 2) := by
  by_cases hn : n = 0
  · simp [hn]
  · have hfirst : 0 < Nat.log 2 (2 * n) := Nat.log_pos (by omega) (by omega)
    have hsecond : 0 < Nat.log 2 (Nat.log 2 (2 * n) + 1) :=
      Nat.log_pos (by omega) (by omega)
    simpa only [Nat.mul_comm 3] using
      (Nat.mul_le_mul_left (n * (Nat.log 2 (2 * n) + 1))
        (show 3 ≤ Nat.log 2 (Nat.log 2 (2 * n) + 1) + 2 by omega))

private theorem cantor_linear_cost_le (n : ℕ) :
    (fastFullMultiplier.{u} n).cost ≤
      893 * n * (Nat.log 2 (2 * n) + 1) *
        (Nat.log 2 (Nat.log 2 (2 * n) + 1) + 2) :=
  fastFullMultiplier_cantor_log_cost_le n

theorem fastFullMultiplier_parameterPreparation_cantor_cost_le (n : ℕ) :
    (fastFullMultiplier.{u} n).parameterPreparation.cost ≤
      893 * n * (Nat.log 2 (2 * n) + 1) *
        (Nat.log 2 (Nat.log 2 (2 * n) + 1) + 2) := by
  rw [(fastFullMultiplier.{u} n).parameterPreparation_cost]
  exact cantor_linear_cost_le n

theorem fastFullMultiplier_linearizedProgram_cantor_cost_le (n : ℕ) :
    (fastFullMultiplier.{u} n).linearizedProgram.cost ≤
      1153 * n * (Nat.log 2 (2 * n) + 1) *
        (Nat.log 2 (Nat.log 2 (2 * n) + 1) + 2) := by
  have h := (fastFullMultiplier.{u} n).linearizedProgram_cost_eq
  have hc := cantor_linear_cost_le n
  have hm := fastFullMultiplier_multiplications_le.{u} n
  have hscale := cantor_log_scale_three n
  nlinarith

theorem fastFullMultiplier_preparedForward_cantor_cost_le (n : ℕ) :
    (fastFullMultiplier.{u} n).preparedForward.cost ≤
      2046 * n * (Nat.log 2 (2 * n) + 1) *
        (Nat.log 2 (Nat.log 2 (2 * n) + 1) + 2) := by
  have h := (fastFullMultiplier.{u} n).preparedForward_cost_eq
  have hc := cantor_linear_cost_le n
  have hm := fastFullMultiplier_multiplications_le.{u} n
  have hscale := cantor_log_scale_three n
  nlinarith

theorem fastFullMultiplier_preparedTranspose_cantor_cost_le (n : ℕ) :
    (fastFullMultiplier.{u} n).preparedTranspose.cost ≤
      3199 * n * (Nat.log 2 (2 * n) + 1) *
        (Nat.log 2 (Nat.log 2 (2 * n) + 1) + 2) + 2 * n := by
  have h := (fastFullMultiplier.{u} n).preparedTranspose_cost_refined
  have hc := cantor_linear_cost_le n
  have hm := fastFullMultiplier_multiplications_le.{u} n
  have hscale := cantor_log_scale_three n
  nlinarith

theorem fastFullMultiplier_linearizedProgram_multiplications_le (n : ℕ) :
    (fastFullMultiplier.{u} n).linearizedProgram.compile.multiplications ≤
      780 * n * (Nat.log 2 (2 * n) + 1) := by
  rw [(fastFullMultiplier.{u} n).linearizedProgram_multiplications]
  have hm := fastFullMultiplier_multiplications_le.{u} n
  calc
    2 * (fastFullMultiplier.{u} n).circuit.multiplications ≤
        2 * (390 * n * (Nat.log 2 (2 * n) + 1)) := Nat.mul_le_mul_left 2 hm
    _ = 780 * n * (Nat.log 2 (2 * n) + 1) := by ring

theorem fastFullMultiplier_preparedForward_multiplications_le (n : ℕ) :
    (fastFullMultiplier.{u} n).preparedForward.multiplications ≤
      1170 * n * (Nat.log 2 (2 * n) + 1) := by
  rw [(fastFullMultiplier.{u} n).preparedForward_multiplications]
  have hm := fastFullMultiplier_multiplications_le.{u} n
  calc
    3 * (fastFullMultiplier.{u} n).circuit.multiplications ≤
        3 * (390 * n * (Nat.log 2 (2 * n) + 1)) := Nat.mul_le_mul_left 3 hm
    _ = 1170 * n * (Nat.log 2 (2 * n) + 1) := by ring

theorem fastFullMultiplier_preparedTranspose_multiplications_le (n : ℕ) :
    (fastFullMultiplier.{u} n).preparedTranspose.multiplications ≤
      1170 * n * (Nat.log 2 (2 * n) + 1) := by
  rw [(fastFullMultiplier.{u} n).preparedTranspose_multiplications]
  have hm := fastFullMultiplier_multiplications_le.{u} n
  calc
    3 * (fastFullMultiplier.{u} n).circuit.multiplications ≤
        3 * (390 * n * (Nat.log 2 (2 * n) + 1)) := Nat.mul_le_mul_left 3 hm
    _ = 1170 * n * (Nat.log 2 (2 * n) + 1) := by ring

theorem fastFullMultiplier_preparedForward_constantBits_le (n : ℕ) :
    (fastFullMultiplier.{u} n).preparedForward.constantBits ≤
      30 * n * (Nat.log 2 (2 * n) + 1) := by
  rw [(fastFullMultiplier.{u} n).preparedForward_constantBits]
  exact fastFullMultiplier_constantBits_le n

theorem fastFullMultiplier_preparedTranspose_constantBits_le (n : ℕ) :
    (fastFullMultiplier.{u} n).preparedTranspose.constantBits ≤
      30 * n * (Nat.log 2 (2 * n) + 1) := by
  rw [(fastFullMultiplier.{u} n).preparedTranspose_constantBits]
  exact fastFullMultiplier_constantBits_le n

end DivisionFree.PolynomialArithmetic
