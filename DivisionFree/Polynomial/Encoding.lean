import DivisionFree.Polynomial.Schoolbook

/-! Reusable facts about the bounded coefficient-vector encoding. -/

namespace DivisionFree
namespace PolynomialArithmetic

theorem vectorPolynomial_coeff_of_lt {R : Type*} [Semiring R]
    (n i : ℕ) (x : Fin n → R) (hi : i < n) :
    (vectorPolynomial n x).coeff i = x ⟨i, hi⟩ := by
  classical
  simpa [vectorPolynomial] using Polynomial.ofFn_coeff_eq_val_of_lt x hi

theorem vectorPolynomial_coeff_eq_zero_of_ge {R : Type*} [Semiring R]
    (n i : ℕ) (x : Fin n → R) (hi : n ≤ i) :
    (vectorPolynomial n x).coeff i = 0 := by
  classical
  simpa [vectorPolynomial] using Polynomial.ofFn_coeff_eq_zero_of_ge x hi

theorem vectorPolynomial_map {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (n : ℕ) (x : Fin n → R) :
    Polynomial.map f (vectorPolynomial n x) =
      vectorPolynomial n (fun i => f (x i)) := by
  classical
  apply Polynomial.ext
  intro i
  by_cases hi : i < n
  · simp [vectorPolynomial_coeff_of_lt, hi]
  · have hni : n ≤ i := Nat.le_of_not_gt hi
    simp [Polynomial.coeff_map, vectorPolynomial_coeff_eq_zero_of_ge, hni]

theorem vectorPolynomial_injective {R : Type*} [Semiring R] (n : ℕ) :
    Function.Injective (vectorPolynomial (R := R) n) := by
  intro x y h
  apply funext
  intro i
  have hc := congrArg (fun p : Polynomial R => p.coeff i.val) h
  simpa [vectorPolynomial_coeff_of_lt] using hc

end PolynomialArithmetic
end DivisionFree
