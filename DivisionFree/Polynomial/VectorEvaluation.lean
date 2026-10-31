import DivisionFree.Polynomial.Encoding

/-! Evaluation and reconstruction of complete bounded coefficient vectors. -/

namespace DivisionFree.PolynomialArithmetic

open scoped BigOperators

theorem vectorPolynomial_coefficients {R : Type*} [Semiring R]
    (n : ℕ) (p : Polynomial R) (hp : ∀ k, n ≤ k → p.coeff k = 0) :
    vectorPolynomial n (fun i => p.coeff i.val) = p := by
  apply Polynomial.ext
  intro k
  by_cases hk : k < n
  · rw [vectorPolynomial_coeff_of_lt n k _ hk]
  · rw [vectorPolynomial_coeff_eq_zero_of_ge n k _ (by omega), hp k (by omega)]

theorem vectorPolynomial_eval₂ {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (n : ℕ) (x : Fin n → R) (w : S) :
    (vectorPolynomial n x).eval₂ f w = ∑ i : Fin n, f (x i) * w ^ i.val := by
  classical
  simp only [vectorPolynomial, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial]

end DivisionFree.PolynomialArithmetic
