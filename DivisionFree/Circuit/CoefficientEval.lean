import DivisionFree.Circuit.Evaluation

/-! Evaluation identities for transporting arithmetic circuits through a ring
homomorphism and for reading the constant coefficient of polynomial-valued
inputs. -/

namespace DivisionFree.Circuit

variable {I O : Type}

/-- Circuit evaluation commutes with every ring homomorphism. -/
theorem eval_map {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (C : Circuit I O) (x : I → R) (o : O) :
    f (C.eval x o) = C.eval (fun i => f (x i)) o := by
  induction C with
  | wire select => rfl
  | zero => simp
  | integer z => simp
  | add => simp [eval_add]
  | neg => simp [eval_neg]
  | mul => simp [eval_mul]
  | comp first second ihFirst ihSecond =>
      simp only [eval_comp_function]
      have hfirst : (fun j => f (first.eval x j)) =
          first.eval (fun i => f (x i)) := by
        funext j
        exact ihFirst x j
      calc
        f (second.eval (first.eval x) o) =
            second.eval (fun j => f (first.eval x j)) o :=
          ihSecond (first.eval x) o
        _ = second.eval (first.eval (fun i => f (x i))) o := by rw [hfirst]
  | pair left right ihLeft ihRight =>
      cases o with
      | inl y =>
          change f (left.eval x y) = left.eval (fun i => f (x i)) y
          exact ihLeft x y
      | inr y =>
          change f (right.eval x y) = right.eval (fun i => f (x i)) y
          exact ihRight x y
  | bundle branches ih =>
      simp only [eval_bundle]
      exact ih o.1 x o.2

/-- The constant coefficient of a polynomial-valued circuit is obtained by
running the same circuit on the constant coefficients of its inputs. -/
theorem eval_coeff_zero {R : Type*} [CommRing R]
    (C : Circuit I O) (x : I → Polynomial R) (o : O) :
    (C.eval x o).coeff 0 = C.eval (fun i => (x i).coeff 0) o := by
  simpa only [Polynomial.constantCoeff_apply] using
    (eval_map (f := Polynomial.constantCoeff) C x o)

end DivisionFree.Circuit

namespace DivisionFree.PolynomialArithmetic

variable {R : Type*} [CommRing R]

/-- The degree-one coefficient of a sum is computed componentwise. -/
theorem coeff_one_add (p q : Polynomial R) :
    (p + q).coeff 1 = p.coeff 1 + q.coeff 1 := by
  simp

/-- Negation acts componentwise on the degree-one coefficient. -/
theorem coeff_one_neg (p : Polynomial R) :
    (-p).coeff 1 = -p.coeff 1 := by
  simp

/-- The degree-one coefficient of a product only depends on the first two
coefficients of its factors. -/
theorem coeff_one_mul (p q : Polynomial R) :
    (p * q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 :=
  Polynomial.mul_coeff_one p q

/-- Integer constants contribute no degree-one coefficient. -/
theorem coeff_one_int (z : ℤ) :
    ((z : Polynomial R).coeff 1) = 0 := by
  change (Polynomial.C (z : R)).coeff 1 = 0
  exact Polynomial.coeff_C_of_ne_zero (by decide)

end DivisionFree.PolynomialArithmetic
