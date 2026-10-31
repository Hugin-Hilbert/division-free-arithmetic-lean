import DivisionFree.Kronecker.MixedRadix
import DivisionFree.Fourier.Scatter
import DivisionFree.Polynomial.CantorMultiplication
import Mathlib.Algebra.Polynomial.BigOperators

/-! A complete full-product wrapper for finite mixed-radix boxes. Every input
coordinate is scattered into the untrimmed product box with side lengths
`2*s-1`, and one ordinary full multiplier is applied to that entire box. -/

namespace DivisionFree.Kronecker


open DivisionFree
open DivisionFree.PolynomialArithmetic
open DivisionFree.Fourier
open Polynomial
open scoped BigOperators

/-- Full convolution side lengths. This includes the final truncation
coordinate without any early clipping. -/
def fullProductRadices (ds : List ℕ) : List ℕ :=
  ds.map (fun s => 2 * s - 1)

def inputSize (ds : List ℕ) : ℕ := capacity ds

def outputSize (ds : List ℕ) : ℕ := capacity (fullProductRadices ds)

def mixedRadixProductExponent (ds : List ℕ) (i : Fin (inputSize ds)) : ℕ :=
  encode (fullProductRadices ds) (digits ds i.val)

private theorem valid_fullRadices_of_valid (ds a : List ℕ) (h : Valid ds a) :
    Valid (fullProductRadices ds) a := by
  induction ds generalizing a with
  | nil => cases a <;> simp_all [Valid, fullProductRadices]
  | cons s ds ih =>
      cases a with
      | nil => simp [Valid] at h
      | cons a as =>
          simp only [Valid, fullProductRadices, List.map_cons]
          refine ⟨?_, ih as h.2⟩
          have ha := h.1
          have hs : 0 < s := by omega
          omega

def mixedRadixScatterIndex (ds : List ℕ) (i : Fin (inputSize ds)) : Fin (outputSize ds) := by
  exact ⟨encode (fullProductRadices ds) (digits ds i.val),
    encode_lt_capacity (fullProductRadices ds) (digits ds i.val)
      (valid_fullRadices_of_valid ds (digits ds i.val)
        (valid_digits ds i.val i.isLt))⟩

@[simp] theorem mixedRadixScatterIndex_val (ds : List ℕ) (i : Fin (inputSize ds)) :
    (mixedRadixScatterIndex ds i).val = mixedRadixProductExponent ds i := rfl

/-- Scatter each input index to the mixed-radix encoding of its full digit
vector, multiply the two scattered arrays, and retain all `M` coefficients
of the product box. -/
noncomputable def fullProductCircuit.{u} (ds : List ℕ) :
    Circuit (Bool × Fin (inputSize ds)) (Fin (outputSize ds)) :=
  .comp
    (.comp (scatter (fun p : Bool × Fin (inputSize ds) =>
        (p.1, mixedRadixScatterIndex ds p.2)))
      ((fastFullMultiplier.{u} (outputSize ds)).circuit))
    (.wire fun k : Fin (outputSize ds) =>
      ⟨k.val, by omega⟩)

theorem fullProductCircuit_cost.{u} (ds : List ℕ) :
    (fullProductCircuit.{u} ds).cost =
      2 * inputSize ds + (fastFullMultiplier.{u} (outputSize ds)).cost := by
  simp only [fullProductCircuit, Circuit.comp_cost, Circuit.wire_cost,
    Nat.add_zero, scatter_cost, FullMultiplier.cost]
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]

theorem fullProductCircuit_constantBits.{u} (ds : List ℕ) :
    (fullProductCircuit.{u} ds).constantBits =
      (fastFullMultiplier.{u} (outputSize ds)).circuit.constantBits := by
  simp only [fullProductCircuit, Circuit.comp_constantBits, Circuit.constantBits,
    scatter_constantBits, Nat.zero_add, Nat.add_zero]

theorem outputSize_le (ds : List ℕ) :
    outputSize ds ≤ 2 ^ ds.length * inputSize ds := by
  induction ds with
  | nil => simp [outputSize, fullProductRadices, inputSize, capacity]
  | cons s ds ih =>
      simp only [outputSize, fullProductRadices, inputSize, List.map_cons,
        capacity, List.length_cons, pow_succ] at *
      have hs : 2 * s - 1 ≤ 2 * s := by omega
      nlinarith

theorem fullProductCircuit_cantor_cost_le (ds : List ℕ) :
    (fullProductCircuit ds).cost ≤
      2 * inputSize ds + 893 * outputSize ds *
        (Nat.log 2 (2 * outputSize ds) + 1) *
          (Nat.log 2 (Nat.log 2 (2 * outputSize ds) + 1) + 2) := by
  rw [fullProductCircuit_cost]
  exact Nat.add_le_add_left (fastFullMultiplier_cantor_log_cost_le (outputSize ds)) _


/-- The ordinary univariate polynomial obtained by scattering the full
mixed-radix digit vectors, before multiplication. -/
noncomputable def kroneckerPolynomial (ds : List ℕ) {R : Type*} [Semiring R]
    (x : Fin (inputSize ds) → R) : Polynomial R :=
  ∑ i : Fin (inputSize ds), Polynomial.C (x i) * X ^ mixedRadixProductExponent ds i

private theorem coeff_C_mul_X_pow (R : Type*) [Semiring R]
    (e k : ℕ) (x : R) :
    (Polynomial.C x * (X : Polynomial R) ^ e).coeff k = if e = k then x else 0 := by
  rw [C_mul_X_pow_eq_monomial]
  simp [Polynomial.coeff_monomial]

private theorem coeff_kroneckerPolynomial (ds : List ℕ) {R : Type*} [CommSemiring R]
    (x : Fin (inputSize ds) → R) (k : ℕ) :
    (kroneckerPolynomial ds x).coeff k =
      ∑ i : Fin (inputSize ds),
        if mixedRadixProductExponent ds i = k then x i else 0 := by
  classical
  simp only [kroneckerPolynomial, ← lcoeff_apply, map_sum]
  simp only [lcoeff_apply]
  simp_rw [coeff_C_mul_X_pow]

private theorem scatter_component_eval (ds : List ℕ) {R : Type*} [CommRing R]
    (x : Bool × Fin (inputSize ds) → R) (b : Bool) (j : Fin (outputSize ds)) :
    (scatter (fun p : Bool × Fin (inputSize ds) =>
      (p.1, mixedRadixScatterIndex ds p.2))).eval x (b, j) =
      ∑ i : Fin (inputSize ds),
        if mixedRadixScatterIndex ds i = j then x (b, i) else 0 := by
  classical
  rw [scatter_eval]
  rw [Fintype.sum_prod_type]
  cases b <;> simp [Prod.mk.injEq]

theorem fullProduct_scatteredPolynomial {R : Type*} [CommRing R]
    (ds : List ℕ) (x : Bool × Fin (inputSize ds) → R) (b : Bool) :
    vectorPolynomial (outputSize ds)
      (fun j => (scatter (fun p : Bool × Fin (inputSize ds) =>
        (p.1, mixedRadixScatterIndex ds p.2))).eval x (b, j)) =
      kroneckerPolynomial ds (fun i => x (b, i)) := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < outputSize ds
  · rw [vectorPolynomial_coeff_of_lt (outputSize ds) k _ hk,
      coeff_kroneckerPolynomial]
    rw [scatter_component_eval]
    simp [Fin.ext_iff, mixedRadixScatterIndex_val]
  · rw [vectorPolynomial_coeff_eq_zero_of_ge (outputSize ds) k _ (Nat.le_of_not_gt hk)]
    rw [coeff_kroneckerPolynomial]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    by_cases heq : mixedRadixProductExponent ds i = k
    · have hlt := (mixedRadixScatterIndex ds i).isLt
      simp [heq] at *
      omega
    · simp [heq]

private theorem coeff_encodedTerm {R : Type*} [CommRing R]
    (a b k : ℕ) (x y : R) :
    (Polynomial.C x * X ^ a * (Polynomial.C y * X ^ b)).coeff k =
      if a + b = k then x * y else 0 := by
  rw [C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial]
  simp [monomial_mul_monomial, coeff_monomial]

private theorem coeff_kronecker_mul (ds : List ℕ) {R : Type*} [CommRing R]
    (x y : Fin (inputSize ds) → R) (k : ℕ) :
    (kroneckerPolynomial ds x * kroneckerPolynomial ds y).coeff k =
      ∑ i : Fin (inputSize ds), ∑ j : Fin (inputSize ds),
        if mixedRadixProductExponent ds i + mixedRadixProductExponent ds j = k
          then x i * y j else 0 := by
  classical
  unfold kroneckerPolynomial
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  simp only [← lcoeff_apply, map_sum]
  simp only [lcoeff_apply]
  simp_rw [coeff_encodedTerm]

/-- Every output slot is the complete convolution of the full mixed-radix
input ranges. The final coordinate is represented with width `2*s-1`, just
like every other coordinate. -/
theorem fullProductCircuit_coeff.{u} {R : Type u} [CommRing R]
    (ds : List ℕ) (x : Bool × Fin (inputSize ds) → R)
    (k : Fin (outputSize ds)) :
    (fullProductCircuit.{u} ds).eval x k =
      ∑ i : Fin (inputSize ds), ∑ j : Fin (inputSize ds),
        if mixedRadixProductExponent ds i + mixedRadixProductExponent ds j = k.val
          then x (false, i) * x (true, j) else 0 := by
  classical
  let f := fun p : Bool × Fin (inputSize ds) =>
    (p.1, mixedRadixScatterIndex ds p.2)
  let y := (scatter f).eval x
  have hm := fastFullMultiplier_correct.{u} (outputSize ds) y
  have hp0 := fullProduct_scatteredPolynomial ds x false
  have hp1 := fullProduct_scatteredPolynomial ds x true
  have hc := congrArg (fun p : Polynomial R => p.coeff k.val) hm
  have hp0' : vectorPolynomial (outputSize ds)
      (fun i => (scatter f).eval x (false, i)) =
      kroneckerPolynomial ds (fun i => x (false, i)) := by simpa [f] using hp0
  have hp1' : vectorPolynomial (outputSize ds)
      (fun i => (scatter f).eval x (true, i)) =
      kroneckerPolynomial ds (fun i => x (true, i)) := by simpa [f] using hp1
  have hk : k.val < outputSize ds := k.isLt
  rw [vectorPolynomial_coeff_of_lt (2 * outputSize ds) k.val _ (by omega)] at hc
  rw [show y = (scatter f).eval x from rfl] at hc
  have heval : (fullProductCircuit.{u} ds).eval x k =
      (fastFullMultiplier.{u} (outputSize ds)).circuit.eval y
        ⟨k.val, by omega⟩ := by
    simp only [fullProductCircuit, Circuit.eval_comp, Circuit.eval_wire]
    rfl
  rw [hp0', hp1'] at hc
  rw [coeff_kronecker_mul] at hc
  exact heval.trans hc

private theorem fullProduct_index_condition_iff (ds : List ℕ)
    (i j : Fin (inputSize ds)) (k : Fin (outputSize ds)) :
    mixedRadixProductExponent ds i + mixedRadixProductExponent ds j = k.val ↔
      digitAdd (digits ds i.val) (digits ds j.val) =
        digits (fullProductRadices ds) k.val := by
  let a := digits ds i.val
  let b := digits ds j.val
  let out := fullProductRadices ds
  have ha : Valid ds a := valid_digits ds i.val i.isLt
  have hb : Valid ds b := valid_digits ds j.val j.isLt
  have hsum : Valid out (digitAdd a b) := valid_digitAdd_double_sub_one ds a b ha hb
  have hout : Valid out (digits out k.val) := valid_digits out k.val k.isLt
  have hencode : encode out (digitAdd a b) =
      mixedRadixProductExponent ds i + mixedRadixProductExponent ds j := by
    exact encode_digitAdd out a b
      (by simp [a, out, fullProductRadices, digits_length])
      (by simp [b, out, fullProductRadices, digits_length])
  have hdecode : encode out (digits out k.val) = k.val := encode_digits out k.val k.isLt
  constructor
  · intro h
    apply encode_injective_on_valid out (digitAdd a b) (digits out k.val) hsum hout
    rw [hencode, hdecode]
    exact h
  · intro h
    have he := congrArg (encode out) h
    rw [hencode, hdecode] at he
    exact he

/-- The same output formula expressed directly as a full multidimensional
convolution: contributing input tuples are exactly those whose coordinatewise
sum equals the decoded output tuple. The no-alias lemmas above ensure distinct
coordinate sums cannot merge in this full `2*s-1` box. -/
theorem fullProductCircuit_digitConvolution.{u} {R : Type u} [CommRing R]
    (ds : List ℕ) (x : Bool × Fin (inputSize ds) → R)
    (k : Fin (outputSize ds)) :
    (fullProductCircuit.{u} ds).eval x k =
      ∑ i : Fin (inputSize ds), ∑ j : Fin (inputSize ds),
        if digitAdd (digits ds i.val) (digits ds j.val) =
          digits (fullProductRadices ds) k.val
        then x (false, i) * x (true, j) else 0 := by
  rw [fullProductCircuit_coeff]
  simp_rw [fullProduct_index_condition_iff]

/-- A pair of input indices can collide in the encoded full product only
when its coordinatewise sum agrees. -/
theorem mixedRadix_pair_no_alias (ds : List ℕ)
    (i j i' j' : Fin (inputSize ds))
    (h : mixedRadixProductExponent ds i + mixedRadixProductExponent ds j =
      mixedRadixProductExponent ds i' + mixedRadixProductExponent ds j') :
    digitAdd (digits ds i.val) (digits ds j.val) =
      digitAdd (digits ds i'.val) (digits ds j'.val) := by
  apply fullProduct_no_alias ds (digits ds i.val) (digits ds j.val)
    (digits ds i'.val) (digits ds j'.val)
  · exact valid_digits ds i.val i.isLt
  · exact valid_digits ds j.val j.isLt
  · exact valid_digits ds i'.val i'.isLt
  · exact valid_digits ds j'.val j'.isLt
  · have h₁ : encode (fullProductRadices ds)
        (digitAdd (digits ds i.val) (digits ds j.val)) =
        mixedRadixProductExponent ds i + mixedRadixProductExponent ds j :=
      encode_digitAdd (fullProductRadices ds) (digits ds i.val) (digits ds j.val)
        (by simp [digits_length, fullProductRadices])
        (by simp [digits_length, fullProductRadices])
    have h₂ : encode (fullProductRadices ds)
        (digitAdd (digits ds i'.val) (digits ds j'.val)) =
        mixedRadixProductExponent ds i' + mixedRadixProductExponent ds j' :=
      encode_digitAdd (fullProductRadices ds) (digits ds i'.val) (digits ds j'.val)
        (by simp [digits_length, fullProductRadices])
        (by simp [digits_length, fullProductRadices])
    change encode (fullProductRadices ds)
      (digitAdd (digits ds i.val) (digits ds j.val)) =
      encode (fullProductRadices ds)
        (digitAdd (digits ds i'.val) (digits ds j'.val))
    rw [h₁, h₂]
    exact h

end DivisionFree.Kronecker
