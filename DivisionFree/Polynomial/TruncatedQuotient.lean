import DivisionFree.Polynomial.TruncatedPairing
import Mathlib.RingTheory.AdjoinRoot

/-! Bridge the bounded coefficient encoding to the polynomial quotient. -/

namespace DivisionFree
namespace PolynomialArithmetic

abbrev TruncatedRing (R : Type*) [CommRing R] (q : ℕ) :=
  AdjoinRoot ((Polynomial.X : Polynomial R) ^ q)

noncomputable def toTruncated {R : Type*} [CommRing R] {q : ℕ}
    (x : Fin q → R) : TruncatedRing R q :=
  AdjoinRoot.mk _ (vectorPolynomial q x)

theorem toTruncated_mulVector {R : Type*} [CommRing R] {q : ℕ}
    (a b : Fin q → R) :
    toTruncated (mulVector a b) = toTruncated a * toTruncated b := by
  classical
  change AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ q)
      (vectorPolynomial q (mulVector a b)) =
    AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ q) (vectorPolynomial q a) *
      AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ q) (vectorPolynomial q b)
  rw [← map_mul (AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ q))]
  rw [AdjoinRoot.mk_eq_mk]
  apply (Polynomial.X_pow_dvd_iff).2
  intro i hi
  have hlt : (vectorPolynomial q (mulVector a b)).coeff i =
      (vectorPolynomial q a * vectorPolynomial q b).coeff i := by
    simp [vectorPolynomial_coeff_of_lt q i (mulVector a b) hi, mulVector]
  rw [Polynomial.coeff_sub, hlt]
  exact sub_self _


theorem toTruncated_zero {R : Type*} [CommRing R] {q : ℕ} :
    toTruncated (R := R) (q := q) (fun _ => 0) = 0 := by
  classical
  change AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ q)
      (vectorPolynomial q (fun _ => 0)) = 0
  rw [AdjoinRoot.mk_eq_zero]
  apply (Polynomial.X_pow_dvd_iff).2
  intro i hi
  rw [vectorPolynomial_coeff_of_lt q i (fun _ => 0) hi]

theorem toTruncated_add {R : Type*} [CommRing R] {q : ℕ}
    (x y : Fin q → R) :
    toTruncated (x + y) = toTruncated x + toTruncated y := by
  classical
  change AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ q)
      (vectorPolynomial q (x + y)) =
    AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ q) (vectorPolynomial q x) +
      AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ q) (vectorPolynomial q y)
  rw [← map_add (AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ q))]
  rw [AdjoinRoot.mk_eq_mk]
  apply (Polynomial.X_pow_dvd_iff).2
  intro i hi
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add,
    vectorPolynomial_coeff_of_lt q i (x + y) hi,
    vectorPolynomial_coeff_of_lt q i x hi,
    vectorPolynomial_coeff_of_lt q i y hi]
  simp

theorem toTruncated_sum {R : Type*} [CommRing R] {q : ℕ} {ι : Type*}
    (t : Finset ι) (f : ι → Fin q → R) :
    toTruncated (∑ i ∈ t, f i) = ∑ i ∈ t, toTruncated (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      change toTruncated (fun _ : Fin q => (0 : R)) = 0
      exact toTruncated_zero
  | @insert i t hit ih =>
      simp [hit, toTruncated_add, ih]

theorem toTruncated_injective {R : Type*} [CommRing R] (q : ℕ) :
    Function.Injective (toTruncated (R := R) (q := q)) := by
  classical
  intro x y hxy
  apply funext
  intro i
  have hdiv : (Polynomial.X : Polynomial R) ^ q ∣
      vectorPolynomial q x - vectorPolynomial q y := by
    exact (AdjoinRoot.mk_eq_mk).1 hxy
  have hcoeff := (Polynomial.X_pow_dvd_iff).1 hdiv i.val i.isLt
  rw [Polynomial.coeff_sub,
    vectorPolynomial_coeff_of_lt q i.val x i.isLt,
    vectorPolynomial_coeff_of_lt q i.val y i.isLt] at hcoeff
  exact sub_eq_zero.mp hcoeff

theorem toTruncated_surjective {R : Type*} [CommRing R] (q : ℕ) :
    Function.Surjective (toTruncated (R := R) (q := q)) := by
  classical
  intro z
  induction z using AdjoinRoot.induction_on with
  | _ p =>
      let x : Fin q → R := fun i => p.coeff i.val
      refine ⟨x, ?_⟩
      change AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ q)
          (vectorPolynomial q x) = AdjoinRoot.mk _ p
      rw [AdjoinRoot.mk_eq_mk]
      apply (Polynomial.X_pow_dvd_iff).2
      intro i hi
      rw [Polynomial.coeff_sub,
        vectorPolynomial_coeff_of_lt q i x hi]
      simp [x]

end PolynomialArithmetic
end DivisionFree
