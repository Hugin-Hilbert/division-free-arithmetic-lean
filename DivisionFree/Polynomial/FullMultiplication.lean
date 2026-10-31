import DivisionFree.Polynomial.Encoding
import DivisionFree.Polynomial.Schoolbook

/-! Full polynomial multiplication by a concrete quadratic schoolbook circuit. -/

namespace DivisionFree
namespace PolynomialArithmetic

universe u

/-- A multiplier that returns all coefficients of the full product. -/
structure FullMultiplier (n : ℕ) where
  circuit : Circuit (Bool × Fin n) (Fin (2 * n))
  correct : ∀ (R : Type u) [CommRing R]
    (x : Bool × Fin n → R),
    vectorPolynomial (2 * n) (circuit.eval x) =
      vectorPolynomial n (fun i => x (false, i)) *
      vectorPolynomial n (fun i => x (true, i))

def FullMultiplier.cost {n : ℕ} (A : FullMultiplier n) : ℕ := A.circuit.cost

def paddedInputs {R : Type*} [Zero R] {n : ℕ} (x : Bool × Fin n → R) :
    Bool × Fin (2 * n) → R := fun (b, i) =>
  if hi : i.val < n then x (b, ⟨i.val, hi⟩) else 0

def paddingCircuit (n : ℕ) :
    Circuit (Bool × Fin n) (Bool × Fin (2 * n)) :=
  .comp
    (.bundle (fun j : Bool × Fin (2 * n) =>
      if hi : j.2.val < n then
        .wire (fun _ : PUnit => (j.1, ⟨j.2.val, hi⟩))
      else .zero))
    (.wire (fun j : Bool × Fin (2 * n) => (j, PUnit.unit)))

theorem paddingCircuit_eval {R : Type*} [Ring R] (n : ℕ)
    (x : Bool × Fin n → R) (j : Bool × Fin (2 * n)) :
    (paddingCircuit n).eval x j = paddedInputs x j := by
  classical
  by_cases hi : j.2.val < n
  · simp [paddingCircuit, paddedInputs, hi, Circuit.eval_comp]
  · simp [paddingCircuit, paddedInputs, hi, Circuit.eval_comp]

theorem vectorPolynomial_paddedInputs {R : Type*} [CommRing R] (n : ℕ)
    (x : Bool × Fin n → R) (b : Bool) :
    vectorPolynomial (2 * n) (fun i => paddedInputs x (b, i)) =
      vectorPolynomial n (fun i => x (b, i)) := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < n
  · rw [vectorPolynomial_coeff_of_lt (2 * n) k _ (by omega),
      vectorPolynomial_coeff_of_lt n k _ hk]
    simp [paddedInputs, hk]
  · by_cases hk2 : k < 2 * n
    · have hnk : n ≤ k := Nat.le_of_not_gt hk
      rw [vectorPolynomial_coeff_of_lt (2 * n) k _ hk2,
        vectorPolynomial_coeff_eq_zero_of_ge n k _ hnk]
      simp [paddedInputs, hk]
    · have h2n : 2 * n ≤ k := Nat.le_of_not_gt hk2
      rw [vectorPolynomial_coeff_eq_zero_of_ge (2 * n) k _ h2n,
        vectorPolynomial_coeff_eq_zero_of_ge n k _ (by omega)]

theorem vectorPolynomial_mul_coeff_eq_zero_of_ge {R : Type*} [CommRing R]
    (n k : ℕ) (x y : Fin n → R) (hk : 2 * n - 1 ≤ k) :
    (vectorPolynomial n x * vectorPolynomial n y).coeff k = 0 := by
  classical
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hsum : ij.1 + ij.2 = k := Finset.mem_antidiagonal.mp hij
  by_cases hi : n ≤ ij.1
  · simp [vectorPolynomial_coeff_eq_zero_of_ge n ij.1 x hi]
  · have hi' : ij.1 < n := Nat.lt_of_not_ge hi
    have hj : n ≤ ij.2 := by omega
    simp [vectorPolynomial_coeff_eq_zero_of_ge n ij.2 y hj]

def fullSchoolbookCircuit (n : ℕ) :
    Circuit (Bool × Fin n) (Fin (2 * n)) :=
  .comp (paddingCircuit n) (schoolbook (2 * n))

theorem fullSchoolbook_correct {R : Type*} [CommRing R] (n : ℕ)
    (x : Bool × Fin n → R) :
    vectorPolynomial (2 * n) ((fullSchoolbookCircuit n).eval x) =
      vectorPolynomial n (fun i => x (false, i)) *
      vectorPolynomial n (fun i => x (true, i)) := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < 2 * n
  · rw [vectorPolynomial_coeff_of_lt (2 * n) k _ hk]
    simp only [fullSchoolbookCircuit, Circuit.eval_comp]
    rw [schoolbook_correct]
    have hpad : (paddingCircuit n).eval x = paddedInputs x := by
      funext j
      exact paddingCircuit_eval n x j
    rw [hpad, vectorPolynomial_paddedInputs n x false,
      vectorPolynomial_paddedInputs n x true]
  · have hk2 : 2 * n ≤ k := Nat.le_of_not_gt hk
    rw [vectorPolynomial_coeff_eq_zero_of_ge (2 * n) k _ hk2,
      vectorPolynomial_mul_coeff_eq_zero_of_ge n k _ _ (by omega)]


theorem fullSchoolbook_last_coeff_zero {R : Type*} [CommRing R] (n : ℕ)
    (hn : 0 < n) (x : Bool × Fin n → R) :
    (fullSchoolbookCircuit n).eval x ⟨2 * n - 1, by omega⟩ = 0 := by
  have hc := congrArg (fun p : Polynomial R => p.coeff (2 * n - 1))
    (fullSchoolbook_correct n x)
  rw [vectorPolynomial_coeff_of_lt (2 * n) (2 * n - 1)
      ((fullSchoolbookCircuit n).eval x) (by omega),
    vectorPolynomial_mul_coeff_eq_zero_of_ge n (2 * n - 1)
      (fun i => x (false, i)) (fun i => x (true, i)) (by omega)] at hc
  exact hc

def fullSchoolbook (n : ℕ) : FullMultiplier n where
  circuit := fullSchoolbookCircuit n
  correct _ _ := fullSchoolbook_correct n

theorem paddingCircuit_cost (n : ℕ) : (paddingCircuit n).cost = 0 := by
  classical
  simp only [paddingCircuit, Circuit.comp_cost, Circuit.bundle_cost,
    Circuit.wire_cost]
  rw [Finset.sum_eq_zero]
  intro j hj
  by_cases hi : j.2.val < n <;> simp [hi]

/-- Exact cost of the padded full-product implementation. -/
theorem fullSchoolbook_cost_exact (n : ℕ) :
    (fullSchoolbook n).cost = 4 * n ^ 2 + 2 * n := by
  rw [show (fullSchoolbook n).cost = (schoolbook (2 * n)).cost by
    simp [fullSchoolbook, FullMultiplier.cost, fullSchoolbookCircuit,
      paddingCircuit_cost], schoolbook_cost_exact]
  ring

theorem fullSchoolbook_cost_le (n : ℕ) :
    (fullSchoolbook n).cost ≤ 8 * n ^ 2 := by
  calc
    (fullSchoolbook n).cost = (schoolbook (2 * n)).cost := by
      simp [fullSchoolbook, FullMultiplier.cost, fullSchoolbookCircuit,
        paddingCircuit_cost]
    _ ≤ 2 * (2 * n) ^ 2 := schoolbook_cost_le (2 * n)
    _ = 8 * n ^ 2 := by ring

end PolynomialArithmetic
end DivisionFree
