import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-!
# Division-free Newton inversion

The update uses only ring operations. Its residual is squared, with no
assumption that 2 is invertible. Polynomial stages truncate after every
update. This module proves correctness; it does not claim a fast circuit
implementation of polynomial multiplication or an operation bound.
-/

namespace DivisionFree.Newton

variable {R : Type*} [CommRing R]

def step (u v : R) : R := v * (2 - u * v)

theorem residual_step (u v : R) : 1 - u * step u v = (1 - u * v) ^ 2 := by
  unfold step
  ring

theorem precision_doubles (t u v : R) (h : ℕ) (hv : t ^ h ∣ 1 - u * v) :
    t ^ (2 * h) ∣ 1 - u * step u v := by
  rw [residual_step, pow_two, show 2 * h = h + h by omega, pow_add]
  exact mul_dvd_mul hv hv

def iterate (u v : R) : ℕ → R
  | 0 => v
  | k + 1 => step u (iterate u v k)

theorem residual_iterate (u v : R) (k : ℕ) :
    1 - u * iterate u v k = (1 - u * v) ^ (2 ^ k) := by
  induction k with
  | zero => simp [iterate]
  | succ k ih => rw [iterate, residual_step, ih, ← pow_mul, pow_succ]

theorem inverse_of_nilpotent_residual (u v : R) (k : ℕ)
    (h : (1 - u * v) ^ (2 ^ k) = 0) : u * iterate u v k = 1 := by
  have he := residual_iterate u v k
  rw [h, sub_eq_zero] at he
  exact he.symm

open Polynomial

/-- Preserve a residual divisibility statement when discarding multiples
of the target modulus. This lemma needs no invertibility hypothesis. -/
theorem residual_mod (u v q : R[X]) (h : q ∣ 1 - u * v) :
    q ∣ 1 - u * (v %ₘ q) := by
  rw [modByMonic_eq_sub_mul_div]
  convert dvd_add h (dvd_mul_right q (u * (v /ₘ q))) using 1
  ring

noncomputable def polynomialInverse (u : R[X]) : ℕ → R[X]
  | 0 => 1
  | k + 1 => step u (polynomialInverse u k) %ₘ (X ^ (2 ^ (k + 1)))

/-- A unit-constant polynomial is inverted to precision `2^k`.
The constant term is normalized to 1, so no scalar inverse is used. -/
theorem polynomialInverse_correct (u : R[X]) (hu : u.coeff 0 = 1) (k : ℕ) :
    (X : R[X]) ^ (2 ^ k) ∣ 1 - u * polynomialInverse u k := by
  induction k with
  | zero => simp only [polynomialInverse, pow_zero, pow_one, mul_one]
            apply X_dvd_iff.mpr
            simp [hu]
  | succ k ih =>
    apply residual_mod
    simpa [pow_succ, Nat.mul_comm] using precision_doubles X u
      (polynomialInverse u k) (2 ^ k) ih

end DivisionFree.Newton
