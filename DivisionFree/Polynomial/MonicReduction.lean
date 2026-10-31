import DivisionFree.Polynomial.MonicRemainder
import DivisionFree.Polynomial.SeriesInverse

/-! Complete monic reduction with charged preparation of the reflected
inverse. Preparation can be shared across any number of dividends. -/

namespace DivisionFree.PolynomialArithmetic

universe u

/-- Retain the lower modulus coefficients and construct the reflected inverse.
The inverse is computed once, using the normalized Newton circuit. -/
noncomputable def monicPrepare (n : ℕ) : Circuit (Fin n) (Fin n ⊕ Fin n) :=
  .pair (.wire id) (.comp (reverseMonicPrefix n) (fastSeriesInverse.{u} n).circuit)

theorem monicPrepare_eval {R : Type u} [CommRing R] (n : ℕ) (a : Fin n → R) :
    (monicPrepare.{u} n).eval a = Sum.elim a
      ((fastSeriesInverse.{u} n).circuit.eval ((reverseMonicPrefix n).eval a)) := by
  simp [monicPrepare, Circuit.eval_pair_function, Circuit.eval_comp_function,
    Circuit.eval_wire_function]

theorem monicPrepare_inverse {R : Type u} [CommRing R] (n : ℕ) (a : Fin n → R) :
    (Polynomial.X : Polynomial R) ^ n ∣
      1 - Polynomial.reflect n (monicPolynomial n a) *
        vectorPolynomial n (fun i => (monicPrepare.{u} n).eval a (Sum.inr i)) := by
  rw [monicPrepare_eval]
  simp only [Sum.elim_inr]
  have h := (fastSeriesInverse.{u} n).correct R ((reverseMonicPrefix n).eval a)
    (by
      intro hn
      rw [vectorPolynomial_coeff_of_lt n 0 _ hn, reverseMonicPrefix_leading n hn])
  rw [reverseMonicPrefix_reflect_mod] at h
  exact (residual_mod_left_iff _ _ _).mp h

theorem monicPrepare_cost (n : ℕ) :
    (monicPrepare.{u} n).cost = (fastSeriesInverse.{u} n).cost := by
  simp [monicPrepare, reverseMonicPrefix_cost, NormalizedSeriesInverse.cost]

theorem monicPrepare_constantBits_le (n : ℕ) :
    (monicPrepare.{u} n).constantBits ≤
      2 + 240 * n * (Nat.log 2 (n + 1) + 3) := by
  have hp := reverseMonicPrefix_constantBits n
  have hi := fastSeriesInverse_constantBits_le.{u} n
  simp only [monicPrepare, Circuit.constantBits, Nat.zero_add]
  omega

/-- Preparation followed by reduction of one full length-`2*n` dividend. -/
noncomputable def monicReductionCircuit (n : ℕ) :
    Circuit (Fin n ⊕ Fin (2 * n)) (Fin n) :=
  .comp (.pair (.comp (.wire Sum.inl) (monicPrepare.{u} n)) (.wire Sum.inr))
    (preparedRemainder.{u} n)

/-- A full monic-remainder implementation with all modulus preparation in
the circuit. The implicit leading coefficient is one. -/
structure MonicReduction (n : ℕ) where
  circuit : Circuit (Fin n ⊕ Fin (2 * n)) (Fin n)
  correct : ∀ (R : Type u) [CommRing R] (a : Fin n → R) (h : Fin (2 * n) → R),
    vectorPolynomial n (circuit.eval (Sum.elim a h)) =
      vectorPolynomial (2 * n) h %ₘ monicPolynomial n a

def MonicReduction.cost {n : ℕ} (A : MonicReduction n) : ℕ := A.circuit.cost

theorem monicReductionCircuit_correct {R : Type u} [CommRing R]
    (n : ℕ) (a : Fin n → R) (h : Fin (2 * n) → R) :
    vectorPolynomial n ((monicReductionCircuit.{u} n).eval (Sum.elim a h)) =
      vectorPolynomial (2 * n) h %ₘ monicPolynomial n a := by
  simp only [monicReductionCircuit, Circuit.eval_comp_function,
    Circuit.eval_pair_function, Circuit.eval_wire_function, Sum.elim_inl, Sum.elim_inr,
    monicPrepare_eval]
  apply preparedRemainder_correct
  simpa only [monicPrepare_eval, Sum.elim_inr] using monicPrepare_inverse n a

/-- Closed monic reduction over every commutative ring. -/
noncomputable def fastMonicReduction (n : ℕ) : MonicReduction.{u} n where
  circuit := monicReductionCircuit.{u} n
  correct _ _ := monicReductionCircuit_correct n

/-- Preparation is charged once; the online phase uses two truncated
products and one vector subtraction. -/
theorem monicReductionCircuit_cost (n : ℕ) :
    (monicReductionCircuit.{u} n).cost =
      (fastSeriesInverse.{u} n).cost + 2 * (fastMultiplier.{u} n).cost + 2 * n := by
  simp [monicReductionCircuit, monicPrepare_cost, preparedRemainder_cost, Nat.add_assoc]

theorem fastMonicReduction_constantBits_le (n : ℕ) :
    (fastMonicReduction.{u} n).circuit.constantBits ≤
      300 * n * (Nat.log 2 (2 * n + 2) + 3) + 2 := by
  have hp := monicPrepare_constantBits_le.{u} n
  have hm := fastMultiplier_constantBits_le.{u} n
  have hlog₁ := Nat.log_mono_right (b := 2) (show n + 1 ≤ 2 * n + 2 by omega)
  have hlog₂ := Nat.log_mono_right (b := 2) (show 2 * n ≤ 2 * n + 2 by omega)
  change (monicReductionCircuit.{u} n).constantBits ≤ _
  simp only [monicReductionCircuit, Circuit.constantBits, Nat.zero_add,
    Nat.add_zero, preparedRemainder_constantBits]
  have hi' := Nat.mul_le_mul_left (240 * n)
    (show Nat.log 2 (n + 1) + 3 ≤ Nat.log 2 (2 * n + 2) + 3 by omega)
  have hm' := Nat.mul_le_mul_left (30 * n)
    (show Nat.log 2 (2 * n) + 1 ≤ Nat.log 2 (2 * n + 2) + 3 by omega)
  nlinarith

end DivisionFree.PolynomialArithmetic
