import DivisionFree.Polynomial.TruncatedMultiplication
import DivisionFree.Polynomial.VectorOperations
import DivisionFree.Newton
import Mathlib.RingTheory.AdjoinRoot

/-! One actual Newton update, charging both multiplication calls and every
coefficient operation. Quotient identities justify intermediate truncation. -/

namespace DivisionFree.PolynomialArithmetic

universe u

/-- Inputs are the polynomial and its current inverse approximation. Each
intermediate product is computed once and shared with the remaining gates. -/
def newtonStepCircuit {n : ℕ} (A : Multiplier.{u} n) :
    Circuit (Bool × Fin n) (Fin n) :=
  .comp (.pair (.wire fun i : Fin n => (true, i)) A.circuit)
    (.comp
      (.pair (.wire fun i : Fin n => Sum.inl i)
        (.comp (.wire fun i : Fin n => Sum.inr i) (twoMinus n)))
      (.comp (.wire fun j : Bool × Fin n => if j.1 then Sum.inr j.2 else Sum.inl j.2)
        A.circuit))

theorem newtonStepCircuit_cost {n : ℕ} (A : Multiplier.{u} n) :
    (newtonStepCircuit A).cost = 2 * A.cost + (twoMinus n).cost := by
  simp [newtonStepCircuit, Multiplier.cost]
  omega

theorem newtonStepCircuit_constantBits {n : ℕ} (A : Multiplier.{u} n) :
    (newtonStepCircuit A).constantBits =
      2 * A.circuit.constantBits + (twoMinus n).constantBits := by
  simp [newtonStepCircuit, Circuit.constantBits]
  omega

theorem newtonStepCircuit_polynomial {n : ℕ} (A : Multiplier.{u} n)
    {R : Type u} [CommRing R] (x : Bool × Fin n → R) :
    vectorPolynomial n ((newtonStepCircuit A).eval x) =
      (vectorPolynomial n (fun i => x (true, i)) *
        ((Polynomial.C (2 : R) -
          (vectorPolynomial n (fun i => x (false, i)) *
            vectorPolynomial n (fun i => x (true, i))) %ₘ (Polynomial.X ^ n)) %ₘ
              (Polynomial.X ^ n))) %ₘ (Polynomial.X ^ n) := by
  have heval : (newtonStepCircuit A).eval x = A.circuit.eval
      (fun j : Bool × Fin n => if j.1 then (twoMinus n).eval (A.circuit.eval x) j.2
        else x (true, j.2)) := by
    funext i
    simp only [newtonStepCircuit, Circuit.eval_comp]
    apply congrArg (fun z : Bool × Fin n → R => A.circuit.eval z i)
    funext j
    rcases j with ⟨b, j⟩
    cases b <;> simp
  rw [heval, A.polynomial_correct]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [vectorPolynomial_twoMinus_mod, A.polynomial_correct]

/-- Remainder does not change a class in the adjoined-root quotient. -/
theorem mk_modByMonic {R : Type*} [CommRing R] (f g : Polynomial R) :
    AdjoinRoot.mk f (g %ₘ f) = AdjoinRoot.mk f g :=
  AdjoinRoot.mk_eq_mk.mpr (Polynomial.dvd_modByMonic_sub g f)

theorem residual_mod_left_iff {R : Type*} [CommRing R] (q u v : Polynomial R) :
    q ∣ 1 - (u %ₘ q) * v ↔ q ∣ 1 - u * v := by
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.mk_eq_zero]
  simp only [map_sub, map_one, map_mul, mk_modByMonic]

theorem newtonStepCircuit_quotient {n : ℕ} (A : Multiplier.{u} n)
    {R : Type u} [CommRing R] (x : Bool × Fin n → R) :
    AdjoinRoot.mk (Polynomial.X ^ n)
        (vectorPolynomial n ((newtonStepCircuit A).eval x)) =
      AdjoinRoot.mk (Polynomial.X ^ n)
        (Newton.step (vectorPolynomial n (fun i => x (false, i)))
          (vectorPolynomial n (fun i => x (true, i)))) := by
  rw [newtonStepCircuit_polynomial]
  simp only [mk_modByMonic, map_mul, map_sub, Newton.step, map_ofNat]

/-- The charged update doubles precision, even when 2 is zero or noninvertible
in the coefficient ring. -/
theorem newtonStepCircuit_residual {n : ℕ} (A : Multiplier.{u} n)
    {R : Type u} [CommRing R] (x : Bool × Fin n → R) (h : ℕ) (hn : n ≤ 2 * h)
    (hx : (Polynomial.X : Polynomial R) ^ h ∣
      1 - vectorPolynomial n (fun i => x (false, i)) *
        vectorPolynomial n (fun i => x (true, i))) :
    (Polynomial.X : Polynomial R) ^ n ∣
      1 - vectorPolynomial n (fun i => x (false, i)) *
        vectorPolynomial n ((newtonStepCircuit A).eval x) := by
  have hstep := Newton.precision_doubles Polynomial.X
    (vectorPolynomial n (fun i => x (false, i)))
    (vectorPolynomial n (fun i => x (true, i))) h hx
  have hdiv : (Polynomial.X : Polynomial R) ^ n ∣
      1 - vectorPolynomial n (fun i => x (false, i)) *
        Newton.step (vectorPolynomial n (fun i => x (false, i)))
          (vectorPolynomial n (fun i => x (true, i))) :=
    dvd_trans (pow_dvd_pow Polynomial.X hn) hstep
  rw [← AdjoinRoot.mk_eq_zero] at hdiv ⊢
  simp only [map_sub, map_one, map_mul] at hdiv ⊢
  rw [newtonStepCircuit_quotient]
  exact hdiv

end DivisionFree.PolynomialArithmetic
