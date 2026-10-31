import DivisionFree.Polynomial.VectorResize
import DivisionFree.Polynomial.VectorReverse
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Monic

/-! Monic polynomial encoding and a circuit for its reflected prefix. -/

namespace DivisionFree.PolynomialArithmetic

open DivisionFree

/-- A monic degree-`n` polynomial represented by its lower coefficients. -/
noncomputable def monicPolynomial {R : Type*} [CommRing R] (n : ℕ) (a : Fin n → R) : Polynomial R :=
  Polynomial.X ^ n + vectorPolynomial n a

theorem monicPolynomial_monic {R : Type*} [CommRing R] (n : ℕ) (a : Fin n → R) :
    (monicPolynomial n a).Monic := by
  classical
  apply Polynomial.monic_X_pow_add
  simpa [vectorPolynomial] using Polynomial.ofFn_degree_lt a

theorem monicPolynomial_degree {R : Type*} [CommRing R] [Nontrivial R]
    (n : ℕ) (a : Fin n → R) : (monicPolynomial n a).degree = n := by
  classical
  rw [monicPolynomial, Polynomial.degree_add_eq_left_of_degree_lt]
  · exact Polynomial.degree_X_pow n
  · rw [Polynomial.degree_X_pow]
    simpa [vectorPolynomial] using (Polynomial.ofFn_degree_lt a)

theorem monicPolynomial_coeff_leading {R : Type*} [CommRing R]
    (n : ℕ) (a : Fin n → R) : (monicPolynomial n a).coeff n = 1 := by
  rw [monicPolynomial, Polynomial.coeff_add, Polynomial.coeff_X_pow_self,
    vectorPolynomial_coeff_eq_zero_of_ge n n a (Nat.le_refl n), add_zero]

theorem monicPolynomial_coeff_below {R : Type*} [CommRing R]
    (n : ℕ) (a : Fin n → R) (k : ℕ) (hk : k < n) :
    (monicPolynomial n a).coeff k = a ⟨k, hk⟩ := by
  rw [monicPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_X_pow, vectorPolynomial_coeff_of_lt n k a hk]
  simp [ne_of_lt hk]

/-- Every monic polynomial is recovered from its lower coefficients and its
implicit leading one, including the zero-ring specialization. -/
theorem monicPolynomial_coefficients {R : Type*} [CommRing R]
    (F : Polynomial R) (hF : F.Monic) :
    monicPolynomial F.natDegree (fun i => F.coeff i.val) = F := by
  classical
  nontriviality R
  apply Polynomial.ext
  intro k
  by_cases hk : k < F.natDegree
  · exact monicPolynomial_coeff_below _ _ k hk
  · by_cases heq : k = F.natDegree
    · subst k
      rw [monicPolynomial_coeff_leading, hF.coeff_natDegree]
    · have hlt : F.natDegree < k := by omega
      rw [monicPolynomial, Polynomial.coeff_add, Polynomial.coeff_X_pow,
        if_neg heq,
        vectorPolynomial_coeff_eq_zero_of_ge _ _ _ (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt hlt, zero_add]

/-- Produce the first `n` coefficients of the reflection of a monic
polynomial, including its implicit leading one. -/
def reverseMonicPrefix (n : ℕ) : Circuit (Fin n) (Fin n) :=
  .comp (.pair (.wire id) (Circuit.integer 1))
    (.comp
      (.bundle fun i : Fin n =>
        if hi : i.val = 0 then
          .wire fun _ : PUnit => Sum.inr PUnit.unit
        else
          .wire fun _ : PUnit => Sum.inl (⟨n - i.val, by omega⟩ : Fin n))
      (.wire fun i : Fin n => (i, PUnit.unit)))

theorem reverseMonicPrefix_eval {R : Type*} [Ring R]
    (n : ℕ) (a : Fin n → R) (i : Fin n) :
    (reverseMonicPrefix n).eval a i =
      if hi : i.val = 0 then 1 else a ⟨n - i.val, by omega⟩ := by
  by_cases hi : i.val = 0 <;> simp [reverseMonicPrefix, hi]

private theorem reverseMonicPrefix_branch_cost (n : ℕ) (i : Fin n) :
    (if h : i.val = 0 then
      (Circuit.wire (fun _ : PUnit => Sum.inr PUnit.unit) : Circuit (Fin n ⊕ PUnit) PUnit)
    else Circuit.wire (fun _ : PUnit => Sum.inl (⟨n - i.val, by omega⟩ : Fin n))).cost = 0 := by
  split_ifs <;> rfl

private theorem reverseMonicPrefix_branch_multiplications (n : ℕ) (i : Fin n) :
    (if h : i.val = 0 then
      (Circuit.wire (fun _ : PUnit => Sum.inr PUnit.unit) : Circuit (Fin n ⊕ PUnit) PUnit)
    else Circuit.wire (fun _ : PUnit => Sum.inl (⟨n - i.val, by omega⟩ : Fin n))).multiplications = 0 := by
  split_ifs <;> rfl

private theorem reverseMonicPrefix_branch_constantBits (n : ℕ) (i : Fin n) :
    (if h : i.val = 0 then
      (Circuit.wire (fun _ : PUnit => Sum.inr PUnit.unit) : Circuit (Fin n ⊕ PUnit) PUnit)
    else Circuit.wire (fun _ : PUnit => Sum.inl (⟨n - i.val, by omega⟩ : Fin n))).constantBits = 0 := by
  split_ifs <;> rfl

theorem reverseMonicPrefix_cost (n : ℕ) :
    (reverseMonicPrefix n).cost = 0 := by
  classical
  simp [reverseMonicPrefix, reverseMonicPrefix_branch_cost]

theorem reverseMonicPrefix_multiplications (n : ℕ) :
    (reverseMonicPrefix n).multiplications = 0 := by
  classical
  simp [reverseMonicPrefix, Circuit.multiplications,
    reverseMonicPrefix_branch_multiplications]

theorem reverseMonicPrefix_constantBits (n : ℕ) :
    (reverseMonicPrefix n).constantBits ≤ 2 := by
  classical
  simp [reverseMonicPrefix, Circuit.constantBits,
    reverseMonicPrefix_branch_constantBits]
  decide

theorem reverseMonicPrefix_leading {R : Type*} [Ring R]
    (n : ℕ) (hn : 0 < n) (a : Fin n → R) :
    (reverseMonicPrefix n).eval a ⟨0, hn⟩ = 1 := by
  simp [reverseMonicPrefix_eval]

theorem reverseMonicPrefix_reflect_mod {R : Type*} [CommRing R]
    (n : ℕ) (a : Fin n → R) :
    vectorPolynomial n ((reverseMonicPrefix n).eval a) =
      Polynomial.reflect n (monicPolynomial n a) %ₘ (Polynomial.X ^ n) := by
  classical
  apply Polynomial.ext
  intro k
  rw [modByMonic_X_pow_coeff]
  by_cases hk : k < n
  · rw [if_pos hk, vectorPolynomial_coeff_of_lt n k _ hk,
      Polynomial.coeff_reflect, Polynomial.revAt_le (by omega : k ≤ n)]
    by_cases hk0 : k = 0
    · subst k
      simp [reverseMonicPrefix_eval, monicPolynomial_coeff_leading]
    · have hbelow : n - k < n := by omega
      simp [reverseMonicPrefix_eval, hk0,
        monicPolynomial_coeff_below n a (n - k) hbelow]
  · rw [if_neg hk, vectorPolynomial_coeff_eq_zero_of_ge n k _ (Nat.le_of_not_gt hk)]

end DivisionFree.PolynomialArithmetic
