import DivisionFree.Polynomial.FullMultiplication
import DivisionFree.Constants

/-! Scaled full multipliers and their explicit Bezout combination. -/

namespace DivisionFree
namespace PolynomialArithmetic

universe u

/-- A concrete full-product circuit whose output is a fixed integer multiple
of the product. -/
structure ScaledFullMultiplier (n : ℕ) (d : ℤ) where
  circuit : Circuit (Bool × Fin n) (Fin (2 * n))
  correct : ∀ (R : Type u) [CommRing R]
    (x : Bool × Fin n → R),
    vectorPolynomial (2 * n) (circuit.eval x) =
      Polynomial.C (d : R) *
        (vectorPolynomial n (fun i => x (false, i)) *
          vectorPolynomial n (fun i => x (true, i)))

private def bezoutPostprocess (n : ℕ) (u v : ℤ) :
    Circuit (Fin (2 * n) ⊕ Fin (2 * n)) (Fin (2 * n)) :=
  .comp (.bundle (fun k =>
    let left : Circuit (Fin (2 * n) ⊕ Fin (2 * n)) PUnit := .comp
      (.pair (.integer u) (.wire (fun _ : PUnit => Sum.inl k)))
      (.comp (.wire (fun b : Bool => if b then Sum.inr PUnit.unit else Sum.inl PUnit.unit)) .mul)
    let right : Circuit (Fin (2 * n) ⊕ Fin (2 * n)) PUnit := .comp
      (.pair (.integer v) (.wire (fun _ : PUnit => Sum.inr k)))
      (.comp (.wire (fun b : Bool => if b then Sum.inr PUnit.unit else Sum.inl PUnit.unit)) .mul)
    Circuit.sum left right)) (.wire fun k : Fin (2 * n) => (k, PUnit.unit))

/-- Combine multipliers with integer factors whose Bezout combination is one.
Each input multiplier is run once, then each coefficient gets two integer
linear operations and one addition. -/
def combineScaledFullMultipliers {n : ℕ} {d e u v : ℤ}
    (A : ScaledFullMultiplier n d) (B : ScaledFullMultiplier n e)
    (hbez : u * d + v * e = 1) : FullMultiplier n where
  circuit := .comp (.pair A.circuit B.circuit) (bezoutPostprocess n u v)
  correct := by
    intro R _ x
    have hA := A.correct R x
    have hB := B.correct R x
    apply Polynomial.ext
    intro k
    by_cases hk : k < 2 * n
    · rw [vectorPolynomial_coeff_of_lt (2 * n) k _ hk]
      have hEval : (bezoutPostprocess n u v).eval
          (Sum.elim (A.circuit.eval x) (B.circuit.eval x)) ⟨k, hk⟩ =
          (u : R) * A.circuit.eval x ⟨k, hk⟩ +
            (v : R) * B.circuit.eval x ⟨k, hk⟩ := by
        simp [bezoutPostprocess, Circuit.eval, Circuit.eval_sum]
      have hcA := congrArg (fun p : Polynomial R => p.coeff k) hA
      have hcB := congrArg (fun p : Polynomial R => p.coeff k) hB
      rw [vectorPolynomial_coeff_of_lt (2 * n) k _ hk] at hcA hcB
      simp only [Polynomial.coeff_C_mul] at hcA hcB
      have hbezR : (u : R) * (d : R) + (v : R) * (e : R) = 1 := by
        simpa only [Int.cast_add, Int.cast_mul, Int.cast_one] using
          congrArg (fun z : ℤ => (z : R)) hbez
      rw [Circuit.eval_comp]
      change (bezoutPostprocess n u v).eval
        (Sum.elim (A.circuit.eval x) (B.circuit.eval x)) ⟨k, hk⟩ = _
      rw [hEval, hcA, hcB]
      calc
        (u : R) * ((d : R) *
            ((vectorPolynomial n (fun i => x (false, i)) *
              vectorPolynomial n (fun i => x (true, i))).coeff k)) +
          (v : R) * ((e : R) *
            ((vectorPolynomial n (fun i => x (false, i)) *
              vectorPolynomial n (fun i => x (true, i))).coeff k)) =
          ((u : R) * (d : R) + (v : R) * (e : R)) *
            ((vectorPolynomial n (fun i => x (false, i)) *
              vectorPolynomial n (fun i => x (true, i))).coeff k) := by ring
        _ = _ := by rw [hbezR, one_mul]
    · have hk' : 2 * n ≤ k := Nat.le_of_not_gt hk
      rw [vectorPolynomial_coeff_eq_zero_of_ge (2 * n) k _ hk']
      exact vectorPolynomial_mul_coeff_eq_zero_of_ge n k
        (fun i => x (false, i)) (fun i => x (true, i)) (by omega) |>.symm

theorem combineScaledFullMultipliers_cost_le {n : ℕ} {d e u v : ℤ}
    (A : ScaledFullMultiplier n d) (B : ScaledFullMultiplier n e)
    (hbez : u * d + v * e = 1) :
    (combineScaledFullMultipliers A B hbez).cost ≤ A.circuit.cost + B.circuit.cost + 6 * n := by
  classical
  simp only [combineScaledFullMultipliers, FullMultiplier.cost, Circuit.comp_cost,
    Circuit.pair_cost]
  unfold bezoutPostprocess
  simp only [Circuit.bundle_cost, Circuit.sum_cost, Circuit.comp_cost,
    Circuit.pair_cost, Circuit.integer_cost, Circuit.wire_cost, Circuit.mul_cost]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  norm_num
  calc
    2 * n * 3 = 6 * n := by ring
    _ ≤ 6 * n := Nat.le_refl _

/-- The actual integer leaves introduced by recombination are charged in
binary. A bound on the chosen Bezout coefficients is a separate obligation. -/
theorem combineScaledFullMultipliers_constantBits {n : ℕ} {d e u v : ℤ}
    (A : ScaledFullMultiplier n d) (B : ScaledFullMultiplier n e)
    (hbez : u * d + v * e = 1) :
    (combineScaledFullMultipliers A B hbez).circuit.constantBits =
      A.circuit.constantBits + B.circuit.constantBits +
        2 * n * (u.natAbs.size + v.natAbs.size + 2) := by
  classical
  simp only [combineScaledFullMultipliers, bezoutPostprocess, Circuit.constantBits, Circuit.sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

end PolynomialArithmetic
end DivisionFree
