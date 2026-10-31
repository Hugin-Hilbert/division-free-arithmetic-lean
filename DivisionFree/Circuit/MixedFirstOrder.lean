import DivisionFree.Circuit.Differential
import DivisionFree.Circuit.TapeCoefficients
import DivisionFree.Polynomial.MixedCoefficients

/-! First-order mixed coefficients of the actual circuit differential. -/

namespace DivisionFree.LinearCircuit

theorem eval_map {K I O : Type} {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (C : LinearCircuit K I O)
    (params : K → R) (input : I → R) (o : O) :
    f (C.eval params input o) =
      C.eval (fun k => f (params k)) (fun i => f (input i)) o := by
  induction C generalizing params with
  | wire select => rfl
  | zero => simp [LinearCircuit.eval]
  | add => simp [LinearCircuit.eval]
  | neg => simp [LinearCircuit.eval]
  | scale c => simp [LinearCircuit.eval]
  | comp first second ihFirst ihSecond =>
      simp only [LinearCircuit.eval_comp]
      have hfirst : (fun j => f (first.eval params input j)) =
          first.eval (fun k => f (params k)) (fun i => f (input i)) := by
        funext j
        exact ihFirst params input j
      calc
        f (second.eval params (first.eval params input) o) =
            second.eval (fun k => f (params k))
              (fun j => f (first.eval params input j)) o :=
          ihSecond params (first.eval params input) o
        _ = second.eval (fun k => f (params k))
              (first.eval (fun k => f (params k)) (fun i => f (input i))) o := by
          rw [hfirst]
  | pair left right ihLeft ihRight =>
      cases o with
      | inl o => exact ihLeft params input o
      | inr o => exact ihRight params input o
  | bundle branches ih => exact ih o.1 params input o.2

end DivisionFree.LinearCircuit

namespace DivisionFree.Circuit

theorem eval_coeff00 {R : Type*} [CommRing R]
    {I O : Type} (C : Circuit I O)
    (x : I → Polynomial (Polynomial R)) (o : O) :
    DivisionFree.PolynomialArithmetic.coeff00 (C.eval x o) =
      C.eval (fun i => DivisionFree.PolynomialArithmetic.coeff00 (x i)) o := by
  simpa [DivisionFree.PolynomialArithmetic.coeff00,
    Polynomial.constantCoeff_apply] using
    (eval_map (f := (Polynomial.constantCoeff : Polynomial R →+* R).comp
      (Polynomial.constantCoeff : Polynomial (Polynomial R) →+* Polynomial R)) C x o)

/-- Inner degree one, outer degree zero is the first-order differential in the
inner polynomial direction. -/
theorem differential_coeff10 {R : Type*} [CommRing R]
    {I O : Type} (C : Circuit I O)
    (x : I → Polynomial (Polynomial R)) (o : O) :
    DivisionFree.PolynomialArithmetic.coeff10 (C.eval x o) =
      (differential C).eval
        (tapeValues C (fun i => DivisionFree.PolynomialArithmetic.coeff00 (x i)))
        (fun i => DivisionFree.PolynomialArithmetic.coeff10 (x i)) o := by
  calc
    DivisionFree.PolynomialArithmetic.coeff10 (C.eval x o) =
        ((C.eval x o).coeff 0).coeff 1 := rfl
    _ = (C.eval (fun i => (x i).coeff 0) o).coeff 1 := by
      rw [eval_coeff_zero]
    _ = _ := by
      simpa [DivisionFree.PolynomialArithmetic.coeff00,
        DivisionFree.PolynomialArithmetic.coeff10] using
        (differential_eval_coeff_one C (fun i => (x i).coeff 0) o)

/-- Inner degree zero, outer degree one is the first-order differential in the
outer polynomial direction. -/
theorem differential_coeff01 {R : Type*} [CommRing R]
    {I O : Type} (C : Circuit I O)
    (x : I → Polynomial (Polynomial R)) (o : O) :
    DivisionFree.PolynomialArithmetic.coeff01 (C.eval x o) =
      (differential C).eval
        (tapeValues C (fun i => DivisionFree.PolynomialArithmetic.coeff00 (x i)))
        (fun i => DivisionFree.PolynomialArithmetic.coeff01 (x i)) o := by
  let params : Tape C → Polynomial R :=
    tapeValues C (fun i => (x i).coeff 0)
  let dirs : I → Polynomial R := fun i => (x i).coeff 1
  have hdiff := differential_eval_coeff_one (R := Polynomial R) C x o
  have hmap := LinearCircuit.eval_map Polynomial.constantCoeff
    (differential C) params dirs o
  have hparams : (fun t => Polynomial.constantCoeff (params t)) =
      tapeValues C (fun i => DivisionFree.PolynomialArithmetic.coeff00 (x i)) := by
    funext t
    exact tapeValues_coeff_zero C (fun i => (x i).coeff 0) t
  calc
    DivisionFree.PolynomialArithmetic.coeff01 (C.eval x o) =
        ((C.eval x o).coeff 1).coeff 0 := rfl
    _ = ((differential C).eval params dirs o).coeff 0 := by
      exact congrArg (fun q : Polynomial R => q.coeff 0) hdiff
    _ = (differential C).eval (fun t => Polynomial.constantCoeff (params t))
          (fun i => Polynomial.constantCoeff (dirs i)) o := hmap
    _ = _ := by
      rw [hparams]
      rfl

end DivisionFree.Circuit
