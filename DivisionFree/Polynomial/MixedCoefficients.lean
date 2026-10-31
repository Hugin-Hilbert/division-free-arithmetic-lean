import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-! Coefficients of bivariate polynomials represented as iterated polynomials. -/

namespace DivisionFree.PolynomialArithmetic

universe u

variable {R : Type u} [CommRing R]

/-- The coefficient of degree zero in both polynomial variables. -/
noncomputable def coeff00 (p : Polynomial (Polynomial R)) : R := (p.coeff 0).coeff 0

/-- Inner degree one and outer degree zero coefficient. -/
noncomputable def coeff10 (p : Polynomial (Polynomial R)) : R := (p.coeff 0).coeff 1

/-- Inner degree zero and outer degree one coefficient. -/
noncomputable def coeff01 (p : Polynomial (Polynomial R)) : R := (p.coeff 1).coeff 0

/-- The coefficient of degree one in both polynomial variables. -/
noncomputable def coeff11 (p : Polynomial (Polynomial R)) : R := (p.coeff 1).coeff 1

theorem coeff00_add (p q : Polynomial (Polynomial R)) :
    coeff00 (p + q) = coeff00 p + coeff00 q := by
  simp [coeff00]

theorem coeff10_add (p q : Polynomial (Polynomial R)) :
    coeff10 (p + q) = coeff10 p + coeff10 q := by
  simp [coeff10]

theorem coeff01_add (p q : Polynomial (Polynomial R)) :
    coeff01 (p + q) = coeff01 p + coeff01 q := by
  simp [coeff01]

theorem coeff11_add (p q : Polynomial (Polynomial R)) :
    coeff11 (p + q) = coeff11 p + coeff11 q := by
  simp [coeff11]

theorem coeff00_neg (p : Polynomial (Polynomial R)) :
    coeff00 (-p) = -coeff00 p := by
  simp [coeff00]

theorem coeff10_neg (p : Polynomial (Polynomial R)) :
    coeff10 (-p) = -coeff10 p := by
  simp [coeff10]

theorem coeff01_neg (p : Polynomial (Polynomial R)) :
    coeff01 (-p) = -coeff01 p := by
  simp [coeff01]

theorem coeff11_neg (p : Polynomial (Polynomial R)) :
    coeff11 (-p) = -coeff11 p := by
  simp [coeff11]

theorem coeff00_mul (p q : Polynomial (Polynomial R)) :
    coeff00 (p * q) = coeff00 p * coeff00 q := by
  simp [coeff00, Polynomial.mul_coeff_zero]

theorem coeff10_mul (p q : Polynomial (Polynomial R)) :
    coeff10 (p * q) = coeff00 p * coeff10 q + coeff10 p * coeff00 q := by
  change ((p * q).coeff 0).coeff 1 = _
  rw [Polynomial.mul_coeff_zero, Polynomial.mul_coeff_one]
  rfl

theorem coeff01_mul (p q : Polynomial (Polynomial R)) :
    coeff01 (p * q) = coeff00 p * coeff01 q + coeff01 p * coeff00 q := by
  change ((p * q).coeff 1).coeff 0 = _
  rw [Polynomial.mul_coeff_one, Polynomial.coeff_add,
    Polynomial.mul_coeff_zero, Polynomial.mul_coeff_zero]
  rfl

theorem coeff11_mul (p q : Polynomial (Polynomial R)) :
    coeff11 (p * q) =
      coeff00 p * coeff11 q + coeff10 p * coeff01 q +
        coeff01 p * coeff10 q + coeff11 p * coeff00 q := by
  unfold coeff00 coeff10 coeff01 coeff11
  rw [Polynomial.mul_coeff_one, Polynomial.coeff_add,
    Polynomial.mul_coeff_one, Polynomial.mul_coeff_one]
  ring

theorem coeff00_int (z : ℤ) : coeff00 (z : Polynomial (Polynomial R)) = (z : R) := by
  simp [coeff00]

theorem coeff10_int (z : ℤ) : coeff10 (z : Polynomial (Polynomial R)) = 0 := by
  change ((Polynomial.C (z : Polynomial R) : Polynomial (Polynomial R)).coeff 0).coeff 1 = 0
  simp only [Polynomial.coeff_C_zero]
  exact Polynomial.coeff_C_of_ne_zero (by decide)

theorem coeff01_int (z : ℤ) : coeff01 (z : Polynomial (Polynomial R)) = 0 := by
  change ((Polynomial.C (z : Polynomial R) : Polynomial (Polynomial R)).coeff 1).coeff 0 = 0
  rw [Polynomial.coeff_C_of_ne_zero (by decide)]
  simp

theorem coeff11_int (z : ℤ) : coeff11 (z : Polynomial (Polynomial R)) = 0 := by
  change ((Polynomial.C (z : Polynomial R) : Polynomial (Polynomial R)).coeff 1).coeff 1 = 0
  rw [Polynomial.coeff_C_of_ne_zero (by decide)]
  simp

end DivisionFree.PolynomialArithmetic
