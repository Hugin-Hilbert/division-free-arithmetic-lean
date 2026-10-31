import DivisionFree.Polynomial.MonicReduction
import DivisionFree.Polynomial.FastMultiplication

/-! Multiplication followed by monic reduction, with the inverse prepared
once and retained for the online product. -/

namespace DivisionFree.PolynomialArithmetic

universe u

/-- Use the retained modulus data and the full product in the prepared
remainder circuit. -/
noncomputable def preparedQuotientProduct (n : ℕ) :
    Circuit ((Fin n ⊕ Fin n) ⊕ (Bool × Fin n)) (Fin n) :=
  .comp
    (.pair (.wire Sum.inl)
      (.comp (.wire Sum.inr) (fastFullMultiplier.{u} n).circuit))
    (preparedRemainder.{u} n)

theorem preparedQuotientProduct_correct {R : Type u} [CommRing R]
    (n : ℕ) (a v : Fin n → R) (x : Bool × Fin n → R)
    (hv : (Polynomial.X : Polynomial R) ^ n ∣
      1 - Polynomial.reflect n (monicPolynomial n a) * vectorPolynomial n v) :
    vectorPolynomial n ((preparedQuotientProduct.{u} n).eval
        (Sum.elim (Sum.elim a v) x)) =
      (vectorPolynomial n (fun i => x (false, i)) *
        vectorPolynomial n (fun i => x (true, i))) %ₘ monicPolynomial n a := by
  simp only [preparedQuotientProduct, Circuit.eval_comp_function,
    Circuit.eval_pair_function, Circuit.eval_wire_function]
  change vectorPolynomial n ((preparedRemainder.{u} n).eval
      (Sum.elim (Sum.elim a v) ((fastFullMultiplier.{u} n).circuit.eval x))) = _
  rw [preparedRemainder_correct n a v
    ((fastFullMultiplier.{u} n).circuit.eval x) hv,
    fastFullMultiplier_correct n x]

theorem preparedQuotientProduct_cost (n : ℕ) :
    (preparedQuotientProduct.{u} n).cost =
      3 * (fastFullMultiplier.{u} n).cost + 2 * n := by
  simp [preparedQuotientProduct, preparedRemainder_cost, fastMultiplier,
    Multiplier.cost, FullMultiplier.truncate, FullMultiplier.cost,
    Circuit.comp_cost, Circuit.pair_cost, Circuit.wire_cost]
  omega

theorem preparedQuotientProduct_constantBits (n : ℕ) :
    (preparedQuotientProduct.{u} n).constantBits =
      3 * (fastFullMultiplier.{u} n).circuit.constantBits := by
  simp [preparedQuotientProduct, preparedRemainder_constantBits,
    fastMultiplier, FullMultiplier.truncate_constantBits, Circuit.constantBits]
  omega

/-- Prepare the monic modulus once, then multiply and reduce any online
input pair of polynomials. -/
noncomputable def quotientProductCircuit (n : ℕ) :
    Circuit (Fin n ⊕ (Bool × Fin n)) (Fin n) :=
  .comp
    (.pair
      (.comp (.wire Sum.inl) (monicPrepare.{u} n))
      (.wire Sum.inr))
    (preparedQuotientProduct.{u} n)

theorem quotientProductCircuit_correct {R : Type u} [CommRing R]
    (n : ℕ) (a : Fin n → R) (x : Bool × Fin n → R) :
    vectorPolynomial n ((quotientProductCircuit.{u} n).eval (Sum.elim a x)) =
      (vectorPolynomial n (fun i => x (false, i)) *
        vectorPolynomial n (fun i => x (true, i))) %ₘ monicPolynomial n a := by
  simp only [quotientProductCircuit, Circuit.eval_comp_function,
    Circuit.eval_pair_function, Circuit.eval_wire_function]
  have hmod : (fun o : Fin n => Sum.elim a x (Sum.inl o)) = a := by
    funext i
    rfl
  have hx : (fun o : Bool × Fin n => Sum.elim a x (Sum.inr o)) = x := by
    funext j
    rfl
  rw [hmod, hx]
  let v : Fin n → R := (fastSeriesInverse.{u} n).circuit.eval
    ((reverseMonicPrefix n).eval a)
  have hv : (Polynomial.X : Polynomial R) ^ n ∣
      1 - Polynomial.reflect n (monicPolynomial n a) * vectorPolynomial n v := by
    have h := monicPrepare_inverse n a
    rw [monicPrepare_eval] at h
    simpa [v] using h
  rw [monicPrepare_eval]
  exact preparedQuotientProduct_correct n a v x hv

theorem quotientProductCircuit_cost (n : ℕ) :
    (quotientProductCircuit.{u} n).cost =
      (fastSeriesInverse.{u} n).cost +
        3 * (fastFullMultiplier.{u} n).cost + 2 * n := by
  simp [quotientProductCircuit, monicPrepare_cost,
    preparedQuotientProduct_cost, Circuit.comp_cost, Circuit.pair_cost,
    Circuit.wire_cost]
  ring

end DivisionFree.PolynomialArithmetic
