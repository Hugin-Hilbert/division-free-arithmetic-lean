import DivisionFree.Circuit.Differential
import DivisionFree.Circuit.TapeCoefficients
import DivisionFree.Circuit.TapeSwap
import DivisionFree.LinearCircuit.Inputs

/-! Propagate the mixed bivariate coefficient linearly, once the two
cross-products at each multiplication gate have been supplied as inputs. -/

namespace DivisionFree.Circuit

open LinearCircuit PolynomialArithmetic

def mixedMultiplication : LinearCircuit Bool (Bool ⊕ Bool) PUnit :=
  .comp
    (.pair (mapInputs Sum.inl multiplicationDifferential)
      (mapInputs Sum.inr (.add : LinearCircuit Bool Bool PUnit)))
    (.comp (.wire (fun b : Bool => if b then Sum.inr PUnit.unit else Sum.inl PUnit.unit))
      .add)

/-- Linear propagation of mixed components; the right input summand stores
one cross-product for each labelled multiplication operand. -/
noncomputable def mixedLinear : {I O : Type} → (C : Circuit I O) →
    LinearCircuit C.Tape (I ⊕ C.Tape) O
  | _, _, .wire select => .wire (fun o => Sum.inl (select o))
  | _, _, .zero => .zero
  | _, _, .integer _ => .zero
  | _, _, .add => mapInputs Sum.inl .add
  | _, _, .neg => mapInputs Sum.inl .neg
  | _, _, .mul => mixedMultiplication
  | _, _, @Circuit.comp _ _ _ inst first second => by
      letI := inst
      exact .comp
        (.pair (mapInputs (Sum.map id Sum.inl) (mapParams Sum.inl (mixedLinear first)))
          (.wire (fun t => Sum.inr (Sum.inr t))))
        (mapParams Sum.inr (mixedLinear second))
  | _, _, .pair left right =>
      .pair (mapInputs (Sum.map id Sum.inl) (mapParams Sum.inl (mixedLinear left)))
        (mapInputs (Sum.map id Sum.inr) (mapParams Sum.inr (mixedLinear right)))
  | _, _, @Circuit.bundle _ J _ inst branches => by
      letI := inst
      exact .bundle (fun j => mapInputs (Sum.map id (Sigma.mk j))
        (mapParams (Sigma.mk j) (mixedLinear (branches j))))

theorem mixedLinear_cost {I O : Type} (C : Circuit I O) :
    C.mixedLinear.cost = C.additions + C.negations + 5 * C.multiplications := by
  induction C with
  | wire _ => rfl
  | zero => rfl
  | integer _ => rfl
  | add => rfl
  | neg => rfl
  | mul => rfl
  | comp first second ihFirst ihSecond =>
      simp [mixedLinear, Tape, LinearCircuit.cost, cost_mapInputs, cost_mapParams,
        Circuit.additions, Circuit.negations, Circuit.multiplications, ihFirst, ihSecond]
      omega
  | pair left right ihLeft ihRight =>
      simp [mixedLinear, Tape, LinearCircuit.cost, cost_mapInputs, cost_mapParams,
        Circuit.additions, Circuit.negations, Circuit.multiplications, ihLeft, ihRight]
      omega
  | bundle branches ih =>
      simp [mixedLinear, Tape, LinearCircuit.cost, cost_mapInputs, cost_mapParams,
        Circuit.additions, Circuit.negations, Circuit.multiplications, ih,
        Finset.sum_add_distrib, Finset.mul_sum]

theorem mixedLinear_multiplications {I O : Type} (C : Circuit I O) :
    C.mixedLinear.multiplications = 2 * C.multiplications := by
  induction C with
  | wire _ => rfl
  | zero => rfl
  | integer _ => rfl
  | add => rfl
  | neg => rfl
  | mul => rfl
  | comp first second ihFirst ihSecond =>
      simp [mixedLinear, Tape, LinearCircuit.multiplications, multiplications_mapInputs,
        multiplications_mapParams, Circuit.multiplications, ihFirst, ihSecond]
      omega
  | pair left right ihLeft ihRight =>
      simp [mixedLinear, Tape, LinearCircuit.multiplications, multiplications_mapInputs,
        multiplications_mapParams, Circuit.multiplications, ihLeft, ihRight]
      omega
  | bundle branches ih =>
      simp [mixedLinear, Tape, LinearCircuit.multiplications, multiplications_mapInputs,
        multiplications_mapParams, Circuit.multiplications, ih, Finset.mul_sum]

/-- Values supplied by the single layer of pairwise cross-products. -/
noncomputable def crossValues {I O : Type} {R : Type*} [CommRing R]
    (C : Circuit I O) (x : I → Polynomial (Polynomial R)) : C.Tape → R :=
  fun t => coeff10 (C.tapeValues x t) * coeff01 (C.tapeValues x (C.tapeSwap t))

theorem mixedLinear_eval_coeff11 {I O : Type} {R : Type*} [CommRing R]
    (C : Circuit I O) (x : I → Polynomial (Polynomial R)) (o : O) :
    coeff11 (C.eval x o) = C.mixedLinear.eval
      (C.tapeValues (fun i => coeff00 (x i)))
      (Sum.elim (fun i => coeff11 (x i)) (C.crossValues x)) o := by
  induction C with
  | wire select => rfl
  | zero => simp [mixedLinear, coeff11]
  | integer z => exact coeff11_int z
  | add => simpa [mixedLinear, mapInputs, LinearCircuit.eval] using
      coeff11_add (x false) (x true)
  | neg => simpa [mixedLinear, mapInputs, LinearCircuit.eval] using
      coeff11_neg (x PUnit.unit)
  | mul =>
      simp only [Circuit.eval_mul, coeff11_mul]
      simp [mixedLinear, Tape, mixedMultiplication, multiplicationDifferential,
        mapInputs, LinearCircuit.eval, crossValues, tapeValues, tapeSwap]
      ring
  | comp first second ihFirst ihSecond =>
      rw [Circuit.eval_comp, ihSecond]
      simp only [mixedLinear, Tape, LinearCircuit.eval_comp, LinearCircuit.eval_mapParams]
      have hz : first.eval (fun i => coeff00 (x i)) =
          fun j => coeff00 (first.eval x j) := by
        funext j
        exact (eval_map (Polynomial.constantCoeff.comp Polynomial.constantCoeff)
          first x j).symm
      change second.mixedLinear.eval
        (second.tapeValues (fun j => coeff00 (first.eval x j)))
        (Sum.elim (fun j => coeff11 (first.eval x j))
          (second.crossValues (first.eval x))) o =
        second.mixedLinear.eval (second.tapeValues (first.eval (fun i => coeff00 (x i))))
          (Sum.elim
            ((mapInputs (Sum.map id Sum.inl) (mapParams Sum.inl first.mixedLinear)).eval
              ((first.comp second).tapeValues (fun i => coeff00 (x i)))
              (Sum.elim (fun i => coeff11 (x i)) ((first.comp second).crossValues x)))
            (fun t => (first.comp second).crossValues x (Sum.inr t))) o
      rw [hz]
      congr 1
      funext z
      cases z with
      | inl j =>
          simp only [Sum.elim_inl, eval_mapInputs, eval_mapParams]
          change coeff11 (first.eval x j) =
            first.mixedLinear.eval (first.tapeValues (fun i => coeff00 (x i)))
              ((Sum.elim (fun i => coeff11 (x i)) ((first.comp second).crossValues x)) ∘
                Sum.map id Sum.inl) j
          have hxin : (Sum.elim (fun i => coeff11 (x i)) ((first.comp second).crossValues x)) ∘
              Sum.map id Sum.inl = Sum.elim (fun i => coeff11 (x i)) (first.crossValues x) := by
            funext t
            cases t <;> rfl
          rw [hxin]
          exact ihFirst x j
      | inr t => rfl
  | pair left right ihLeft ihRight =>
      cases o with
      | inl o =>
          rw [Circuit.eval_pair_inl, ihLeft]
          simp only [mixedLinear, Tape, LinearCircuit.eval_pair_inl, eval_mapInputs, eval_mapParams]
          congr 1
          funext t
          cases t <;> rfl
      | inr o =>
          rw [Circuit.eval_pair_inr, ihRight]
          simp only [mixedLinear, Tape, LinearCircuit.eval_pair_inr, eval_mapInputs, eval_mapParams]
          congr 1
          funext t
          cases t <;> rfl
  | bundle branches ih =>
      rw [Circuit.eval_bundle, ih]
      simp only [mixedLinear, Tape, LinearCircuit.eval_bundle, eval_mapInputs, eval_mapParams]
      congr 1
      funext t
      cases t <;> rfl

end DivisionFree.Circuit
