import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic

/-! Degree and reflection facts used by reverse-polynomial division. -/

namespace DivisionFree.PolynomialArithmetic

open Polynomial

/-- A degree bound below twice the modulus degree bounds the monic quotient
below one modulus degree. -/
theorem monicDivision_degree_bounds {R : Type*} [CommRing R] [Nontrivial R]
    {n : ℕ} (hn : 0 < n) (F h : Polynomial R)
    (hFmonic : F.Monic) (hFdegree : F.degree = (n : WithBot ℕ))
    (hh : h.degree < ((2 * n : ℕ) : WithBot ℕ)) :
    (h /ₘ F).natDegree ≤ n - 1 ∧ (h %ₘ F).degree < (n : WithBot ℕ) := by
  have hFne : F ≠ 0 := hFmonic.ne_zero
  have hFnd : F.natDegree = n := by
    exact_mod_cast (show (F.natDegree : WithBot ℕ) = (n : WithBot ℕ) by
      rw [← Polynomial.degree_eq_natDegree hFne, hFdegree])
  have hhnat : h.natDegree < 2 * n := by
    by_cases hh0 : h = 0
    · simp [hh0, hn]
    · exact Polynomial.natDegree_lt_iff_degree_lt hh0 |>.2 hh
  have hq : (h /ₘ F).natDegree ≤ n - 1 := by
    rw [Polynomial.natDegree_divByMonic h hFmonic, hFnd]
    omega
  have hr : (h %ₘ F).degree < (n : WithBot ℕ) := by
    simpa [hFdegree] using Polynomial.degree_modByMonic_lt h hFmonic
  exact ⟨hq, hr⟩

/-- Reversing a remainder of degree below `n`, within a `2*n-1` window,
produces a polynomial divisible by `X^n`. -/
theorem reflect_monicRemainder_dvd {R : Type*} [CommRing R] [Nontrivial R]
    {n : ℕ} (hn : 0 < n) (F h : Polynomial R)
    (hFmonic : F.Monic) (hFdegree : F.degree = (n : WithBot ℕ))
    (hh : h.degree < ((2 * n : ℕ) : WithBot ℕ)) :
    X ^ n ∣ Polynomial.reflect (2 * n - 1) (h %ₘ F) := by
  have hr := (monicDivision_degree_bounds hn F h hFmonic hFdegree hh).2
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  have hdle : d ≤ 2 * n - 1 := by omega
  rw [Polynomial.coeff_reflect, Polynomial.revAt_le hdle]
  have hrev : n ≤ 2 * n - 1 - d := by omega
  apply Polynomial.coeff_eq_zero_of_degree_lt
  exact hr.trans_le (by exact_mod_cast hrev)

/-- Division by a monic polynomial becomes multiplication after reflection,
up to a term divisible by `X^n`. -/
theorem reflect_monicDivision_congruence {R : Type*} [CommRing R] [Nontrivial R]
    {n : ℕ} (hn : 0 < n) (F h : Polynomial R)
    (hFmonic : F.Monic) (hFdegree : F.degree = (n : WithBot ℕ))
    (hh : h.degree < ((2 * n : ℕ) : WithBot ℕ)) :
    X ^ n ∣ Polynomial.reflect (2 * n - 1) h -
      Polynomial.reflect n F * Polynomial.reflect (n - 1) (h /ₘ F) := by
  have hbounds := monicDivision_degree_bounds hn F h hFmonic hFdegree hh
  have hFnd : F.natDegree = n := by
    have hFne : F ≠ 0 := hFmonic.ne_zero
    exact_mod_cast (show (F.natDegree : WithBot ℕ) = (n : WithBot ℕ) by
      rw [← Polynomial.degree_eq_natDegree hFne, hFdegree])
  have hdecomp : h = h %ₘ F + F * (h /ₘ F) :=
    (Polynomial.modByMonic_add_div h F).symm
  have hreflect := congrArg (Polynomial.reflect (2 * n - 1)) hdecomp
  rw [Polynomial.reflect_add] at hreflect
  have hexp : n + (n - 1) = 2 * n - 1 := by omega
  have hmul := Polynomial.reflect_mul F (h /ₘ F)
    (by rw [hFnd]) hbounds.1
  rw [hexp] at hmul
  have hcong : Polynomial.reflect (2 * n - 1) h -
      Polynomial.reflect n F * Polynomial.reflect (n - 1) (h /ₘ F) =
        Polynomial.reflect (2 * n - 1) (h %ₘ F) := by
    rw [hreflect, hmul]
    ring
  rw [hcong]
  exact reflect_monicRemainder_dvd hn F h hFmonic hFdegree hh

end DivisionFree.PolynomialArithmetic
