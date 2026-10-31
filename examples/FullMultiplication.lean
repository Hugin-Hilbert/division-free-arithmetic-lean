import DivisionFree.Polynomial.FastMultiplication

open DivisionFree.PolynomialArithmetic

example {R : Type} [CommRing R] (n : ℕ) (x : Bool × Fin n → R) :
    vectorPolynomial (2 * n) ((fastFullMultiplier.{0} n).circuit.eval x) =
      vectorPolynomial n (fun i => x (false, i)) *
        vectorPolynomial n (fun i => x (true, i)) := by
  exact fastFullMultiplier_correct n x
