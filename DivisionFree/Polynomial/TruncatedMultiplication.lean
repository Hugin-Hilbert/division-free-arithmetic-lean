import DivisionFree.Polynomial.FastMultiplication

/-! Truncated multiplication obtained by projecting a concrete full product. -/

namespace DivisionFree.PolynomialArithmetic

universe u

/-- Project a full product circuit to the low `n` coefficients. -/
def FullMultiplier.truncate {n : ℕ} (A : FullMultiplier.{u} n) : Multiplier.{u} n where
  circuit := .comp A.circuit (.wire fun j : Fin n => Fin.castLE (by omega) j)
  correct R _ x j := by
    have h := congrArg (fun p : Polynomial R => p.coeff j.val) (A.correct R x)
    rw [vectorPolynomial_coeff_of_lt (2 * n) j.val (A.circuit.eval x) (by omega)] at h
    simpa [Circuit.eval_comp, Fin.castLE] using h

@[simp] theorem FullMultiplier.truncate_cost {n : ℕ} (A : FullMultiplier.{u} n) :
    A.truncate.cost = A.cost := by
  rfl

@[simp] theorem FullMultiplier.truncate_constantBits {n : ℕ}
    (A : FullMultiplier.{u} n) : A.truncate.circuit.constantBits = A.circuit.constantBits := by
  simp [FullMultiplier.truncate, Circuit.constantBits]

/-- The unconditional fast full multiplier, projected to its low coefficients. -/
noncomputable def fastMultiplier (n : ℕ) : Multiplier.{u} n :=
  (fastFullMultiplier.{u} n).truncate

theorem fastMultiplier_correct {R : Type u} [CommRing R]
    (n : ℕ) (x : Bool × Fin n → R) (j : Fin n) :
    (fastMultiplier.{u} n).circuit.eval x j =
      (vectorPolynomial n (fun i => x (false, i)) *
        vectorPolynomial n (fun i => x (true, i))).coeff j.val :=
  (fastMultiplier.{u} n).correct R x j

theorem fastMultiplier_constantBits_le (n : ℕ) :
    (fastMultiplier n).circuit.constantBits ≤ 30 * n * (Nat.log 2 (2 * n) + 1) := by
  simpa [fastMultiplier] using fastFullMultiplier_constantBits_le n

/-- A truncated multiplier computes the product remainder modulo `X^n`. -/
theorem Multiplier.polynomial_correct {n : ℕ} (A : Multiplier.{u} n)
    {R : Type u} [CommRing R] (x : Bool × Fin n → R) :
    vectorPolynomial n (A.circuit.eval x) =
      (vectorPolynomial n (fun i => x (false, i)) *
        vectorPolynomial n (fun i => x (true, i))) %ₘ (Polynomial.X ^ n) := by
  classical
  let out := vectorPolynomial n (A.circuit.eval x)
  let prod := vectorPolynomial n (fun i => x (false, i)) *
    vectorPolynomial n (fun i => x (true, i))
  have hcoeff (k : ℕ) (hk : k < n) : out.coeff k = prod.coeff k := by
    simpa [out, prod, vectorPolynomial_coeff_of_lt n k (A.circuit.eval x) hk] using
      A.correct R x ⟨k, hk⟩
  have hdiv : (Polynomial.X : Polynomial R) ^ n ∣ prod - out := by
    rw [Polynomial.X_pow_dvd_iff]
    intro k hk
    simp only [Polynomial.coeff_sub, hcoeff k hk, sub_self]
  by_cases hR : Nontrivial R
  · letI := hR
    have hdeg : out.degree < Polynomial.degree ((Polynomial.X : Polynomial R) ^ n) := by
      rw [Polynomial.degree_X_pow]
      simpa [out, vectorPolynomial] using Polynomial.ofFn_degree_lt (A.circuit.eval x)
    have hmod := Polynomial.modByMonic_eq_of_dvd_sub
      (Polynomial.monic_X_pow (R := R) n) hdiv
    have hout := (Polynomial.modByMonic_eq_self_iff
      (Polynomial.monic_X_pow (R := R) n)).2 hdeg
    change out = prod %ₘ (Polynomial.X ^ n)
    rw [← hout]
    exact hmod.symm
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    exact Subsingleton.elim _ _

end DivisionFree.PolynomialArithmetic
