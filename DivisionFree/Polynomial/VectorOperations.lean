import DivisionFree.Polynomial.Encoding
import DivisionFree.Polynomial.VectorResize
import DivisionFree.Constants

/-! Concrete pointwise operations on bounded coefficient vectors. -/

namespace DivisionFree.PolynomialArithmetic

open DivisionFree

/-- Pointwise addition of two length-`n` vectors. -/
def vectorAdd (n : ℕ) : Circuit (Bool × Fin n) (Fin n) :=
  .comp
    (.bundle fun i : Fin n => Circuit.sum
      (.wire fun _ : PUnit => (false, i))
      (.wire fun _ : PUnit => (true, i)))
    (.wire fun i => (i, PUnit.unit))

/-- Pointwise subtraction of two length-`n` vectors. -/
def vectorSub (n : ℕ) : Circuit (Bool × Fin n) (Fin n) :=
  .comp
    (.bundle fun i : Fin n => Circuit.sum
      (.wire fun _ : PUnit => (false, i))
      (Circuit.negative (.wire fun _ : PUnit => (true, i))))
    (.wire fun i => (i, PUnit.unit))

/-- The vector of coefficients of `2 - u`, with the constant term supplied
as an explicit integer leaf and all other entries computed by negation. -/
def twoMinus (n : ℕ) : Circuit (Fin n) (Fin n) :=
  .comp
    (.bundle fun i : Fin n => Circuit.sum
      (if i.val = 0 then (.integer 2 : Circuit (Fin n) PUnit) else .zero)
      (Circuit.negative (.wire fun _ : PUnit => i)))
    (.wire fun i => (i, PUnit.unit))

@[simp] theorem vectorAdd_eval {R : Type*} [Ring R] (n : ℕ)
    (x : Bool × Fin n → R) (i : Fin n) :
    (vectorAdd n).eval x i = x (false, i) + x (true, i) := by
  simp [vectorAdd]

@[simp] theorem vectorSub_eval {R : Type*} [Ring R] (n : ℕ)
    (x : Bool × Fin n → R) (i : Fin n) :
    (vectorSub n).eval x i = x (false, i) - x (true, i) := by
  simp [vectorSub, sub_eq_add_neg]

@[simp] theorem twoMinus_eval {R : Type*} [CommRing R] (n : ℕ)
    (x : Fin n → R) (i : Fin n) :
    (twoMinus n).eval x i = (if i.val = 0 then 2 else 0) - x i := by
  by_cases hi : i.val = 0 <;> simp [twoMinus, hi, sub_eq_add_neg]

theorem vectorAdd_cost (n : ℕ) : (vectorAdd n).cost = n := by
  classical
  simp [vectorAdd]

theorem vectorSub_cost (n : ℕ) : (vectorSub n).cost = 2 * n := by
  classical
  simp [vectorSub]
  omega

theorem vectorAdd_constantBits (n : ℕ) : (vectorAdd n).constantBits = 0 := by
  classical
  simp [vectorAdd, Circuit.constantBits, Circuit.sum]

theorem vectorSub_constantBits (n : ℕ) : (vectorSub n).constantBits = 0 := by
  classical
  simp [vectorSub, Circuit.constantBits, Circuit.sum, Circuit.negative]

theorem twoMinus_cost_le (n : ℕ) : (twoMinus n).cost ≤ 2 * n := by
  classical
  simp only [twoMinus, Circuit.comp_cost, Circuit.bundle_cost, Circuit.wire_cost]
  simp only [Circuit.sum_cost, Circuit.negative_cost, Circuit.wire_cost]
  have hleft : ∀ i : Fin n,
      (if i.val = 0 then (Circuit.integer 2 : Circuit (Fin n) PUnit) else .zero).cost = 0 := by
    intro i
    by_cases hi : i.val = 0 <;> simp [hi]
  simp only [hleft]
  simp
  omega

theorem twoMinus_constantBits_le (n : ℕ) : (twoMinus n).constantBits ≤ 3 := by
  classical
  simp only [twoMinus, Circuit.comp_constantBits, Circuit.constantBits]
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let i0 : Fin n := ⟨0, hnpos⟩
    rw [Finset.sum_eq_single i0]
    · have hi0 : i0.val = 0 := rfl
      have hsize : Nat.size 2 = 2 := by decide
      simp [Circuit.constantBits, Circuit.sum, Circuit.negative, hi0, hsize]
    · intro i hi hne
      have hiz : i.val ≠ 0 := by
        intro h
        apply hne
        exact Fin.ext h
      simp [Circuit.constantBits, Circuit.sum, Circuit.negative, hiz]
    · simp

/-- Coefficientwise, `twoMinus` represents subtraction from the constant
polynomial `2`. -/
theorem vectorPolynomial_twoMinus_coeff {R : Type*} [CommRing R]
    (n : ℕ) (x : Fin n → R) (i : Fin n) :
    (vectorPolynomial n ((twoMinus n).eval x)).coeff i.val =
      (Polynomial.C (2 : R) - vectorPolynomial n x).coeff i.val := by
  simp [vectorPolynomial_coeff_of_lt, twoMinus_eval, Polynomial.coeff_sub,
    Polynomial.coeff_C]

/-- As a polynomial representative, `twoMinus` is the remainder of `2-u`
modulo `X^n`, including the empty-vector case `n=0`. -/
theorem vectorPolynomial_twoMinus_mod {R : Type*} [CommRing R]
    (n : ℕ) (x : Fin n → R) :
    vectorPolynomial n ((twoMinus n).eval x) =
      (Polynomial.C (2 : R) - vectorPolynomial n x) %ₘ (Polynomial.X ^ n) := by
  classical
  apply Polynomial.ext
  intro k
  rw [modByMonic_X_pow_coeff]
  by_cases hk : k < n
  · rw [if_pos hk]
    calc
      (vectorPolynomial n ((twoMinus n).eval x)).coeff k =
          (Polynomial.C (2 : R) - vectorPolynomial n x).coeff k :=
        vectorPolynomial_twoMinus_coeff n x ⟨k, hk⟩
      _ = (Polynomial.C (2 : R) - vectorPolynomial n x).coeff k := rfl
  · rw [if_neg hk]
    exact vectorPolynomial_coeff_eq_zero_of_ge n k _ (Nat.le_of_not_gt hk)

/-- Pointwise vector addition agrees exactly with polynomial addition. -/
theorem vectorPolynomial_vectorAdd {R : Type*} [CommRing R]
    (n : ℕ) (x : Bool × Fin n → R) :
    vectorPolynomial n ((vectorAdd n).eval x) =
      vectorPolynomial n (fun i => x (false, i)) +
        vectorPolynomial n (fun i => x (true, i)) := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < n
  · rw [vectorPolynomial_coeff_of_lt n k _ hk, vectorAdd_eval,
      Polynomial.coeff_add,
      vectorPolynomial_coeff_of_lt n k (fun i => x (false, i)) hk,
      vectorPolynomial_coeff_of_lt n k (fun i => x (true, i)) hk]
  · rw [vectorPolynomial_coeff_eq_zero_of_ge n k _ (Nat.le_of_not_gt hk),
      Polynomial.coeff_add,
      vectorPolynomial_coeff_eq_zero_of_ge n k (fun i => x (false, i))
        (Nat.le_of_not_gt hk),
      vectorPolynomial_coeff_eq_zero_of_ge n k (fun i => x (true, i))
        (Nat.le_of_not_gt hk)]
    simp

/-- Pointwise vector subtraction agrees exactly with polynomial subtraction. -/
theorem vectorPolynomial_vectorSub {R : Type*} [CommRing R]
    (n : ℕ) (x : Bool × Fin n → R) :
    vectorPolynomial n ((vectorSub n).eval x) =
      vectorPolynomial n (fun i => x (false, i)) -
        vectorPolynomial n (fun i => x (true, i)) := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < n
  · rw [vectorPolynomial_coeff_of_lt n k _ hk, vectorSub_eval,
      Polynomial.coeff_sub,
      vectorPolynomial_coeff_of_lt n k (fun i => x (false, i)) hk,
      vectorPolynomial_coeff_of_lt n k (fun i => x (true, i)) hk]
  · rw [vectorPolynomial_coeff_eq_zero_of_ge n k _ (Nat.le_of_not_gt hk),
      Polynomial.coeff_sub,
      vectorPolynomial_coeff_eq_zero_of_ge n k (fun i => x (false, i))
        (Nat.le_of_not_gt hk),
      vectorPolynomial_coeff_eq_zero_of_ge n k (fun i => x (true, i))
        (Nat.le_of_not_gt hk)]
    simp

end DivisionFree.PolynomialArithmetic
