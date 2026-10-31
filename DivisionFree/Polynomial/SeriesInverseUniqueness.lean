import DivisionFree.Polynomial.TruncatedQuotient
import Mathlib.RingTheory.AdjoinRoot

/-! Uniqueness and coefficient consequences for inverses modulo `X^n`. -/

namespace DivisionFree.PolynomialArithmetic

open Polynomial

/-- Two right inverses of the same element modulo a polynomial are equal
modulo that polynomial, over any commutative ring. -/
theorem eq_mod_of_left_inverse_mod {R : Type*} [CommRing R]
    (q u v w : Polynomial R)
    (huv : q ∣ 1 - u * v) (huw : q ∣ 1 - u * w) : q ∣ v - w := by
  let π : Polynomial R →+* AdjoinRoot q := AdjoinRoot.mk q
  have huv' : π 1 = π (u * v) := (AdjoinRoot.mk_eq_mk).2 huv
  have huw' : π 1 = π (u * w) := (AdjoinRoot.mk_eq_mk).2 huw
  have hprodv : π u * π v = 1 := by
    calc
      π u * π v = π (u * v) := (map_mul π u v).symm
      _ = π 1 := huv'.symm
      _ = 1 := map_one π
  have hprodw : π u * π w = 1 := by
    calc
      π u * π w = π (u * w) := (map_mul π u w).symm
      _ = π 1 := huw'.symm
      _ = 1 := map_one π
  have hvw : π v = π w := by
    calc
      π v = π v * 1 := by simp
      _ = π v * (π u * π w) := by rw [hprodw]
      _ = (π u * π v) * π w := by ring
      _ = π w := by rw [hprodv]; simp
  exact (AdjoinRoot.mk_eq_mk).1 hvw

/-- Normalized inverses of one polynomial modulo `X^n` have the same
coefficient vector. This includes `n = 0` and the zero ring. -/
theorem normalizedSeriesInverse_unique {R : Type*} [CommRing R]
    (n : ℕ) (u : Polynomial R) (v w : Fin n → R)
    (hv : (Polynomial.X : Polynomial R) ^ n ∣
      1 - u * vectorPolynomial n v)
    (hw : (Polynomial.X : Polynomial R) ^ n ∣
      1 - u * vectorPolynomial n w) : v = w := by
  have hdiff : (Polynomial.X : Polynomial R) ^ n ∣
      vectorPolynomial n v - vectorPolynomial n w :=
    eq_mod_of_left_inverse_mod ((Polynomial.X : Polynomial R) ^ n) u
      (vectorPolynomial n v) (vectorPolynomial n w) hv hw
  have hclass : toTruncated v = toTruncated w := by
    change AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ n) (vectorPolynomial n v) =
      AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ n) (vectorPolynomial n w)
    exact (AdjoinRoot.mk_eq_mk).2 hdiff
  exact toTruncated_injective n hclass

/-- A normalized inverse modulo `X^n` has the prescribed product coefficients
below degree `n`. -/
theorem normalizedSeriesInverse_coeff {R : Type*} [CommRing R]
    (n : ℕ) (u : Polynomial R) (v : Fin n → R)
    (h : (Polynomial.X : Polynomial R) ^ n ∣
      1 - u * vectorPolynomial n v) (i : Fin n) :
    (u * vectorPolynomial n v).coeff i.val =
      if i.val = 0 then 1 else 0 := by
  have hzero := (Polynomial.X_pow_dvd_iff.mp h) i.val i.isLt
  rw [Polynomial.coeff_sub] at hzero
  have hcoeff : (1 : Polynomial R).coeff i.val =
      if i.val = 0 then 1 else 0 := Polynomial.coeff_one
  rw [hcoeff] at hzero
  exact (sub_eq_zero.mp hzero).symm

end DivisionFree.PolynomialArithmetic
