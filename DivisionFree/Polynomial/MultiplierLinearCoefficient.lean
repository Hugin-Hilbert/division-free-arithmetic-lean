import DivisionFree.Circuit.CoefficientEval
import DivisionFree.Polynomial.FullMultiplication
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-! Coefficient semantics for a multiplier on a linearized right input. -/

namespace DivisionFree
namespace PolynomialArithmetic

universe u

private def coeff01Hom (R : Type u) [CommRing R] :
    Polynomial R →+* TrivSqZeroExt R R where
  toFun p := (p.coeff 0, p.coeff 1)
  map_one' := by
    apply TrivSqZeroExt.ext
    · simp
    · change (Polynomial.C (1 : R)).coeff 1 = 0
      exact Polynomial.coeff_C_of_ne_zero (by decide)
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · exact Polynomial.mul_coeff_zero p q
    · exact Polynomial.mul_coeff_one p q
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' p q := by apply TrivSqZeroExt.ext <;> simp

noncomputable def multiplierLinearInput {n : ℕ} {R : Type u} [CommRing R]
    (a b : Fin n → R) : Bool × Fin n → Polynomial R := fun z =>
  if z.1 then Polynomial.C (b z.2) * Polynomial.X else Polynomial.C (a z.2)

private def dualInput {n : ℕ} {R : Type u} [CommRing R]
    (a b : Fin n → R) : Bool × Fin n → TrivSqZeroExt R R := fun z =>
  if z.1 then TrivSqZeroExt.inr (b z.2) else TrivSqZeroExt.inl (a z.2)

private theorem coeff01Hom_linearInput {n : ℕ} {R : Type u} [CommRing R]
    (a b : Fin n → R) :
    (fun z => coeff01Hom R (multiplierLinearInput a b z)) = dualInput a b := by
  funext z
  by_cases hz : z.1 <;> simp [multiplierLinearInput, dualInput, coeff01Hom, hz,
    TrivSqZeroExt.inl, TrivSqZeroExt.inr]

private theorem coeff_product_snd {n j : ℕ} {R : Type u} [CommRing R]
    (a b : Fin n → R) :
    (Polynomial.coeff (vectorPolynomial n (fun i => TrivSqZeroExt.inl (a i)) *
       vectorPolynomial n (fun i => TrivSqZeroExt.inr (b i))) j).snd =
      (Polynomial.coeff (vectorPolynomial n a * vectorPolynomial n b) j) := by
  classical
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  rw [TrivSqZeroExt.snd_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  by_cases hi : ij.1 < n <;> by_cases hk : ij.2 < n
  · simp [vectorPolynomial_coeff_of_lt, hi, hk]
  · simp [vectorPolynomial_coeff_of_lt, vectorPolynomial_coeff_eq_zero_of_ge,
      hi, Nat.le_of_not_gt hk]
  · simp [vectorPolynomial_coeff_of_lt, vectorPolynomial_coeff_eq_zero_of_ge,
      Nat.le_of_not_gt hi, hk]
  · simp [vectorPolynomial_coeff_eq_zero_of_ge,
      Nat.le_of_not_gt hi, Nat.le_of_not_gt hk]

theorem FullMultiplier.coeff_one_fixedLeft {n : ℕ} (A : FullMultiplier.{u} n)
    {R : Type u} [CommRing R] (a b : Fin n → R) (j : Fin (2 * n)) :
    ((A.circuit.eval (multiplierLinearInput a b)) j).coeff 1 =
      A.circuit.eval (fun z => if z.1 then b z.2 else a z.2) j := by
  classical
  let f := coeff01Hom R
  have hmap := Circuit.eval_map (f := f) A.circuit (multiplierLinearInput a b) j
  have hinput := coeff01Hom_linearInput a b
  rw [hinput] at hmap
  change (f ((A.circuit.eval (multiplierLinearInput a b)) j)).snd = _
  have hsnd := congrArg TrivSqZeroExt.snd hmap
  rw [hsnd]
  have hcorrect := A.correct (TrivSqZeroExt R R) (dualInput a b)
  have hc := congrArg (fun p : Polynomial (TrivSqZeroExt R R) => p.coeff j.val) hcorrect
  rw [vectorPolynomial_coeff_of_lt (2 * n) j.val _ j.isLt] at hc
  rw [hc]
  have hcoef := coeff_product_snd (n := n) (j := j.val) a b
  have hcoef' :
      (((vectorPolynomial n fun i => dualInput a b (false, i)) *
        vectorPolynomial n fun i => dualInput a b (true, i)).coeff j.val).snd =
        (vectorPolynomial n a * vectorPolynomial n b).coeff j.val := by
    simpa [dualInput] using hcoef
  rw [hcoef']
  have hcorrectR := A.correct R (fun z => if z.1 then b z.2 else a z.2)
  have hcR := congrArg (fun p : Polynomial R => p.coeff j.val) hcorrectR
  rw [vectorPolynomial_coeff_of_lt (2 * n) j.val _ j.isLt] at hcR
  exact hcR.symm

theorem FullMultiplier.zero_right {n : ℕ} (A : FullMultiplier.{u} n)
    {R : Type u} [CommRing R] (a : Fin n → R) (j : Fin (2 * n)) :
    A.circuit.eval (fun z => if z.1 then 0 else a z.2) j = 0 := by
  classical
  have hcorrect := A.correct R (fun z => if z.1 then 0 else a z.2)
  have hc := congrArg (fun p : Polynomial R => p.coeff j.val) hcorrect
  rw [vectorPolynomial_coeff_of_lt (2 * n) j.val _ j.isLt] at hc
  have hzero : vectorPolynomial n (fun i : Fin n => (0 : R)) = 0 := by
    apply Polynomial.ext
    intro k
    by_cases hk : k < n
    · simp [vectorPolynomial_coeff_of_lt, hk]
    · simp [vectorPolynomial_coeff_eq_zero_of_ge, Nat.le_of_not_gt hk]
  have hright : vectorPolynomial n
      (fun i : Fin n => if (true, i).1 then 0 else a (true, i).2) = 0 := by
    simpa using hzero
  rw [hright, mul_zero, Polynomial.coeff_zero] at hc
  exact hc

end PolynomialArithmetic
end DivisionFree
