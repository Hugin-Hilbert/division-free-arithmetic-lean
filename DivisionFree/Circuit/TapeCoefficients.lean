import DivisionFree.Circuit.Tape
import DivisionFree.Circuit.CoefficientEval
import DivisionFree.Polynomial.MixedCoefficients

/-! Coefficient maps act pointwise on the operand values recorded by tapes. -/

namespace DivisionFree.Circuit

theorem tapeValues_map {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) {I O : Type} (C : Circuit I O)
    (x : I → R) (t : Tape C) :
    f (tapeValues C x t) = tapeValues C (fun i => f (x i)) t := by
  induction C with
  | wire _ => exact Empty.elim t
  | zero => exact Empty.elim t
  | integer _ => exact Empty.elim t
  | add => exact Empty.elim t
  | neg => exact Empty.elim t
  | mul => rfl
  | comp first second ihFirst ihSecond =>
      cases t with
      | inl t => exact ihFirst x t
      | inr t =>
          simp only [tapeValues]
          have hfirst : (fun j => f (first.eval x j)) =
              first.eval (fun i => f (x i)) := by
            funext j
            exact eval_map f first x j
          calc
            f (second.tapeValues (first.eval x) t) =
                second.tapeValues (fun j => f (first.eval x j)) t :=
              ihSecond (first.eval x) t
            _ = second.tapeValues (first.eval (fun i => f (x i))) t := by
              rw [hfirst]
  | pair left right ihLeft ihRight =>
      cases t with
      | inl t => exact ihLeft x t
      | inr t => exact ihRight x t
  | bundle branches ih =>
      cases t with
      | mk j t => exact ih j x t

theorem tapeValues_coeff_zero {R : Type*} [CommRing R]
    {I O : Type} (C : Circuit I O) (x : I → Polynomial R) (t : Tape C) :
    (tapeValues C x t).coeff 0 =
      tapeValues C (fun i => (x i).coeff 0) t := by
  simpa only [Polynomial.constantCoeff_apply] using
    (tapeValues_map (f := Polynomial.constantCoeff) C x t)

theorem tapeValues_coeff00 {R : Type*} [CommRing R]
    {I O : Type} (C : Circuit I O)
    (x : I → Polynomial (Polynomial R)) (t : Tape C) :
    DivisionFree.PolynomialArithmetic.coeff00 (tapeValues C x t) =
      tapeValues C (fun i => DivisionFree.PolynomialArithmetic.coeff00 (x i)) t := by
  let f : Polynomial (Polynomial R) →+* R :=
    (Polynomial.constantCoeff : Polynomial R →+* R).comp
      (Polynomial.constantCoeff : Polynomial (Polynomial R) →+* Polynomial R)
  have h := tapeValues_map f C x t
  simpa [f, DivisionFree.PolynomialArithmetic.coeff00,
    Polynomial.constantCoeff_apply] using h

end DivisionFree.Circuit
