import DivisionFree.Polynomial.NewtonInverse

/-! Quasi-linear normalized series inversion at every requested precision.
The input constant coefficient is one; no ring element is inverted. -/

namespace DivisionFree.PolynomialArithmetic

universe u

/-- An inverse implementation includes an actual circuit. Precision zero has
no normalization requirement and yields the unique empty vector. -/
structure NormalizedSeriesInverse (n : ℕ) where
  circuit : Circuit (Fin n) (Fin n)
  correct : ∀ (R : Type u) [CommRing R] (x : Fin n → R),
    (0 < n → (vectorPolynomial n x).coeff 0 = 1) →
    (Polynomial.X : Polynomial R) ^ n ∣
      1 - vectorPolynomial n x * vectorPolynomial n (circuit.eval x)

def NormalizedSeriesInverse.cost {n : ℕ} (A : NormalizedSeriesInverse n) : ℕ := A.circuit.cost

/-- Pad to a dyadic precision, run the charged Newton recursion, and discard
the extra coefficients. All padding and projection operations are wires. -/
noncomputable def seriesInverseCircuit (n : ℕ) : Circuit (Fin n) (Fin n) :=
  if n = 0 then .zero else
    .comp (resize n (2 ^ Nat.clog 2 n))
      (.comp (inversePowerCircuit.{u} (Nat.clog 2 n)) (resize (2 ^ Nat.clog 2 n) n))

theorem seriesInverseCircuit_correct {R : Type u} [CommRing R]
    (n : ℕ) (x : Fin n → R) (hx : 0 < n → (vectorPolynomial n x).coeff 0 = 1) :
    (Polynomial.X : Polynomial R) ^ n ∣
      1 - vectorPolynomial n x * vectorPolynomial n ((seriesInverseCircuit.{u} n).eval x) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hpad := (dyadicPadding_bounds (by omega : 1 ≤ n)).1
    let y := (resize n (2 ^ Nat.clog 2 n)).eval x
    let v := (inversePowerCircuit.{u} (Nat.clog 2 n)).eval y
    have hy : vectorPolynomial (2 ^ Nat.clog 2 n) y = vectorPolynomial n x :=
      vectorPolynomial_resize_eq_of_le hpad x
    have hy0 : (vectorPolynomial (2 ^ Nat.clog 2 n) y).coeff 0 = 1 := by
      rw [hy, hx hnpos]
    have hrec := inversePowerCircuit_correct (Nat.clog 2 n) y hy0
    rw [hy] at hrec
    have hsmall : (Polynomial.X : Polynomial R) ^ n ∣
        1 - vectorPolynomial n x * vectorPolynomial (2 ^ Nat.clog 2 n) v :=
      dvd_trans (pow_dvd_pow Polynomial.X hpad) hrec
    have hout : (seriesInverseCircuit.{u} n).eval x =
        (resize (2 ^ Nat.clog 2 n) n).eval v := by
      funext i
      simp only [seriesInverseCircuit, if_neg hn, Circuit.eval_comp, v, y]
    rw [hout, vectorPolynomial_resize_mod]
    exact Newton.residual_mod _ _ _ hsmall

/-- Closed normalized inversion over arbitrary commutative rings, including
the zero ring and zero precision. -/
noncomputable def fastSeriesInverse (n : ℕ) : NormalizedSeriesInverse.{u} n where
  circuit := seriesInverseCircuit.{u} n
  correct _ _ x := seriesInverseCircuit_correct n x

theorem seriesInverseCircuit_constantBits_le (n : ℕ) :
    (seriesInverseCircuit.{u} n).constantBits ≤ 240 * n * (Nat.log 2 (n + 1) + 3) := by
  by_cases hn : n = 0
  · simp [seriesInverseCircuit, hn, Circuit.constantBits]
  · simp only [seriesInverseCircuit, if_neg hn, Circuit.comp_constantBits,
      resize_constantBits, Nat.add_zero, Nat.zero_add]
    exact newtonBits_dyadic_bound (fun j => (inversePowerCircuit.{u} j).constantBits)
      (le_of_eq inversePowerCircuit_base_constantBits)
      inversePowerCircuit_step_constantBits_le (by omega)

theorem fastSeriesInverse_constantBits_le (n : ℕ) :
    (fastSeriesInverse.{u} n).circuit.constantBits ≤ 240 * n * (Nat.log 2 (n + 1) + 3) :=
  seriesInverseCircuit_constantBits_le n

end DivisionFree.PolynomialArithmetic
