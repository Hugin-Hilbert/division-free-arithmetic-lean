import DivisionFree.Polynomial.Encoding
import DivisionFree.Constants

/-! Resize finite coefficient vectors by truncating or zero-padding. -/

namespace DivisionFree

open PolynomialArithmetic

/-- Resize a coefficient vector, padding with zeros when the target is longer. -/
def resize (n m : ℕ) : Circuit (Fin n) (Fin m) :=
  .comp
    (.bundle (fun i : Fin m =>
      if h : i.val < n then
        .wire (fun _ : PUnit => (⟨i.val, h⟩ : Fin n))
      else .zero))
    (.wire (fun i : Fin m => (i, PUnit.unit)))

@[simp] theorem resize_eval {R : Type*} [Ring R]
    (n m : ℕ) (x : Fin n → R) (i : Fin m) :
    (resize n m).eval x i = if h : i.val < n then x ⟨i.val, h⟩ else 0 := by
  by_cases h : i.val < n <;> simp [resize, h]

theorem resize_cost (n m : ℕ) : (resize n m).cost = 0 := by
  classical
  simp [resize]
  intro i
  split_ifs <;> simp

theorem resize_multiplications (n m : ℕ) :
    (resize n m).multiplications = 0 := by
  classical
  simp [resize]
  intro i
  split_ifs <;> simp

theorem resize_constantBits (n m : ℕ) :
    (resize n m).constantBits = 0 := by
  classical
  simp [resize, Circuit.constantBits]
  intro i
  split_ifs <;> simp [Circuit.constantBits]

/-- Coefficients below `m` survive reduction modulo `X^m`, and all higher
coefficients vanish. -/
theorem modByMonic_X_pow_coeff {R : Type*} [CommRing R]
    (p : Polynomial R) (m k : ℕ) :
    (p %ₘ (Polynomial.X ^ m)).coeff k = if k < m then p.coeff k else 0 := by
  by_cases hkm : k < m
  · have hrel := congrArg (fun q : Polynomial R => q.coeff k)
      (Polynomial.modByMonic_add_div p (Polynomial.X ^ m))
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul'] at hrel
    simp only [if_neg (by omega : ¬m ≤ k), add_zero] at hrel
    simpa [hkm] using hrel
  · have hmk : m ≤ k := Nat.le_of_not_gt hkm
    by_cases hm : m = 0
    · subst m
      simp [Polynomial.modByMonic_one]
    · nontriviality R
      have hdeg : (p %ₘ (Polynomial.X ^ m)).degree < (m : WithBot ℕ) := by
        simpa [Polynomial.degree_X_pow] using
          (Polynomial.degree_modByMonic_lt p (Polynomial.monic_X_pow m))
      rw [if_neg hkm]
      exact Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by exact_mod_cast hmk))

/-- Resizing a coefficient vector is polynomial remainder modulo `X^m`. -/
theorem vectorPolynomial_resize_mod {R : Type*} [CommRing R]
    (n m : ℕ) (x : Fin n → R) :
    vectorPolynomial m ((resize n m).eval x) =
      vectorPolynomial n x %ₘ (Polynomial.X ^ m) := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hkm : k < m
  · rw [vectorPolynomial_coeff_of_lt m k _ hkm,
      modByMonic_X_pow_coeff]
    simp only [if_pos hkm]
    rw [resize_eval]
    by_cases hkn : k < n
    · simp [hkn, vectorPolynomial_coeff_of_lt n k x hkn]
    · have hnk : n ≤ k := Nat.le_of_not_gt hkn
      simp [hkn, vectorPolynomial_coeff_eq_zero_of_ge n k x hnk]
  · rw [vectorPolynomial_coeff_eq_zero_of_ge m k _ (Nat.le_of_not_gt hkm),
      modByMonic_X_pow_coeff]
    simp [hkm]

/-- If the target vector is at least as long, resizing preserves its polynomial. -/
theorem vectorPolynomial_resize_eq_of_le {R : Type*} [CommRing R]
    {n m : ℕ} (hnm : n ≤ m) (x : Fin n → R) :
    vectorPolynomial m ((resize n m).eval x) = vectorPolynomial n x := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hkn : k < n
  · have hkm : k < m := lt_of_lt_of_le hkn hnm
    rw [vectorPolynomial_coeff_of_lt m k _ hkm,
      vectorPolynomial_coeff_of_lt n k x hkn]
    simp [resize_eval, hkn]
  · have hnk : n ≤ k := Nat.le_of_not_gt hkn
    by_cases hkm : k < m
    · rw [vectorPolynomial_coeff_of_lt m k _ hkm,
        vectorPolynomial_coeff_eq_zero_of_ge n k x hnk]
      simp [resize_eval, hkn]
    · rw [vectorPolynomial_coeff_eq_zero_of_ge m k _ (Nat.le_of_not_gt hkm),
        vectorPolynomial_coeff_eq_zero_of_ge n k x hnk]

/-- Under truncation, each coefficient below the cutoff is retained and every
coefficient at or above the cutoff is dropped. -/
theorem vectorPolynomial_truncate_coeff {R : Type*} [CommRing R]
    {m n : ℕ} (hmn : m ≤ n) (x : Fin n → R) (k : ℕ) :
    (vectorPolynomial n x %ₘ (Polynomial.X ^ m)).coeff k =
      if h : k < m then x ⟨k, lt_of_lt_of_le h hmn⟩ else 0 := by
  rw [modByMonic_X_pow_coeff]
  split_ifs with h
  · simp [vectorPolynomial_coeff_of_lt n k x (lt_of_lt_of_le h hmn)]
  · rfl

/-- Resizing twice agrees with a direct resize if both steps only pad. -/
theorem resize_comp_eval_of_le {n m k : ℕ} (hkm : k ≤ m)
    {R : Type*} [Ring R] (x : Fin n → R) (i : Fin k) :
    (resize m k).eval ((resize n m).eval x) i = (resize n k).eval x i := by
  have hik : i.val < m := lt_of_lt_of_le i.isLt hkm
  simp [resize_eval, hik]

/-- Resizing twice agrees with a direct resize if the first step already
contains every nonzero coefficient, regardless of the final target length. -/
theorem resize_comp_eval_of_le_input {n m k : ℕ} (hnm : n ≤ m)
    {R : Type*} [Ring R] (x : Fin n → R) (i : Fin k) :
    (resize m k).eval ((resize n m).eval x) i = (resize n k).eval x i := by
  by_cases hik : i.val < m
  · simp [resize_eval, hik]
  · have hin : ¬ i.val < n := by omega
    simp [resize_eval, hik, hin]

end DivisionFree
