import DivisionFree.Fourier.Polynomial
import DivisionFree.Fourier.CyclicCircuits
import DivisionFree.Polynomial.Encoding

/-!
# Zero-padded input circuits for cyclic coefficient arrays
-/

namespace DivisionFree.Fourier

open DivisionFree

/-- Embed a length-`n` vector into a cyclic coefficient array, padding by zero. -/
noncomputable def cyclicInput (n m : ℕ) [NeZero m] :
    Circuit (Bool × Fin n) (Bool × ZMod m) :=
  .comp
    (.bundle fun o : Bool × ZMod m =>
      if h : o.2.val < n then
        .wire fun _ : PUnit => (o.1, ⟨o.2.val, h⟩)
      else .zero)
    (.wire fun o : Bool × ZMod m => (o, PUnit.unit))

@[simp] theorem cyclicInput_eval {R : Type*} [Ring R] {n m : ℕ} [NeZero m]
    (x : Bool × Fin n → R) (b : Bool) (j : ZMod m) :
    (cyclicInput n m).eval x (b, j) =
      if h : j.val < n then x (b, ⟨j.val, h⟩) else 0 := by
  by_cases h : j.val < n <;> simp [cyclicInput, h]

theorem cyclicInput_cost (n m : ℕ) [NeZero m] :
    (cyclicInput n m).cost = 0 := by
  classical
  simp only [cyclicInput, Circuit.comp_cost, Circuit.bundle_cost, Circuit.wire_cost]
  apply Finset.sum_eq_zero
  intro o ho
  split_ifs <;> simp

theorem cyclicInput_multiplications (n m : ℕ) [NeZero m] :
    (cyclicInput n m).multiplications = 0 := by
  classical
  simp only [cyclicInput, Circuit.comp_multiplications,
    Circuit.bundle_multiplications, Circuit.wire_multiplications]
  apply Finset.sum_eq_zero
  intro o ho
  split_ifs <;> simp

theorem cyclicInput_constantBits (n m : ℕ) [NeZero m] :
    (cyclicInput n m).constantBits = 0 := by
  classical
  simp only [cyclicInput, Circuit.comp_constantBits, Circuit.constantBits]
  apply Finset.sum_eq_zero
  intro o ho
  split_ifs <;> simp [Circuit.constantBits]

theorem cyclicInput_toPolynomial {R : Type*} [CommRing R]
    (n m : ℕ) [NeZero m] (hnm : n ≤ m)
    (x : Bool × Fin n → R) (b : Bool) :
    toPolynomial (fun j => (cyclicInput n m).eval x (b, j)) =
      PolynomialArithmetic.vectorPolynomial n (fun i => x (b, i)) := by
  classical
  let p := PolynomialArithmetic.vectorPolynomial n (fun i => x (b, i))
  have hcoeff (j : ZMod m) :
      (cyclicInput n m).eval x (b, j) = p.coeff j.val := by
    rw [cyclicInput_eval (R := R)]
    by_cases h : j.val < n
    · simp [p, h, PolynomialArithmetic.vectorPolynomial_coeff_of_lt n j.val _ h]
    · simp [p, h, PolynomialArithmetic.vectorPolynomial_coeff_eq_zero_of_ge n j.val _ (by omega)]
  have hfun : (fun j : ZMod m => (cyclicInput n m).eval x (b, j)) =
      fun j => p.coeff j.val := funext hcoeff
  rw [hfun]
  apply toPolynomial_coefficients p
  intro k hk
  dsimp [p]
  exact PolynomialArithmetic.vectorPolynomial_coeff_eq_zero_of_ge n k _ (by omega)

end DivisionFree.Fourier
