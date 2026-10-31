import DivisionFree.Circuit.CoefficientEval
import DivisionFree.Circuit.Tape
import DivisionFree.LinearCircuit.Rename

/-! First-order coefficient extraction for arithmetic circuits. -/

namespace DivisionFree.Circuit

open LinearCircuit

/-- The linear circuit for the differential of one multiplication gate. The
two coefficient parameters are the constant terms of the two inputs. -/
def multiplicationDifferential : LinearCircuit Bool Bool PUnit :=
  .comp
    (.pair
      (.comp (.wire (fun _ : PUnit => true)) (.scale false))
      (.comp (.wire (fun _ : PUnit => false)) (.scale true)))
    (.comp
      (.wire (fun b : Bool => if b then Sum.inr PUnit.unit else Sum.inl PUnit.unit))
      .add)

/-- Replace each multiplication gate by its first-order differential, with
the constant values of its multiplication inputs supplied as parameters. -/
def differential : {I O : Type} → (C : Circuit I O) → LinearCircuit (Tape C) I O
  | _, _, .wire select => .wire select
  | _, _, .zero => .zero
  | _, _, .integer _ => .zero
  | _, _, .add => .add
  | _, _, .neg => .neg
  | _, _, .mul => multiplicationDifferential
  | _, _, @Circuit.comp _ _ _ _ first second =>
      .comp (mapParams (K := Tape first) (L := Tape first ⊕ Tape second)
          Sum.inl (differential first))
        (mapParams (K := Tape second) (L := Tape first ⊕ Tape second)
          Sum.inr (differential second))
  | _, _, .pair left right =>
      .pair (mapParams (K := Tape left) (L := Tape left ⊕ Tape right)
          Sum.inl (differential left))
        (mapParams (K := Tape right) (L := Tape left ⊕ Tape right)
          Sum.inr (differential right))
  | _, _, @Circuit.bundle _ J _ _ branches =>
      .bundle (fun j => mapParams (K := Tape (branches j))
        (L := Sigma (fun k : J => Tape (branches k)))
        (fun t : Tape (branches j) => (⟨j, t⟩ : Sigma (fun k : J => Tape (branches k))))
        (differential (branches j)))

private theorem tapeValues_comp {I J O : Type} [Fintype J] {R : Type*} [Ring R]
    (first : Circuit I J) (second : Circuit J O) (x : I → R) :
    tapeValues (Circuit.comp first second) x =
      fun t : Tape first ⊕ Tape second =>
        match t with
        | .inl t => tapeValues first x t
        | .inr t => tapeValues second (first.eval x) t := by
  funext t
  cases t <;> rfl

private theorem tapeValues_pair {I O P : Type} {R : Type*} [Ring R]
    (left : Circuit I O) (right : Circuit I P) (x : I → R) :
    tapeValues (Circuit.pair left right) x =
      fun t : Tape left ⊕ Tape right =>
        match t with
        | .inl t => tapeValues left x t
        | .inr t => tapeValues right x t := by
  funext t
  cases t <;> rfl

private theorem tapeValues_bundle {I J O : Type} [Fintype J] {R : Type*} [Ring R]
    (branches : J → Circuit I O) (x : I → R) :
    tapeValues (Circuit.bundle branches) x =
      fun t : Sigma (fun j : J => Tape (branches j)) =>
        tapeValues (branches t.1) x t.2 := by
  funext t
  rfl

theorem differential_cost {I O : Type} (C : Circuit I O) :
    (differential C).cost = C.additions + C.negations + 3 * C.multiplications := by
  induction C with
  | wire _ => simp [differential, LinearCircuit.cost, Circuit.additions,
      Circuit.negations, Circuit.multiplications]
  | zero => simp [differential, LinearCircuit.cost, Circuit.additions,
      Circuit.negations, Circuit.multiplications]
  | integer _ => simp [differential, LinearCircuit.cost, Circuit.additions,
      Circuit.negations, Circuit.multiplications]
  | add => simp [differential, LinearCircuit.cost, Circuit.additions,
      Circuit.negations, Circuit.multiplications]
  | neg => simp [differential, LinearCircuit.cost, Circuit.additions,
      Circuit.negations, Circuit.multiplications]
  | mul => simp [differential, multiplicationDifferential, LinearCircuit.cost,
      Circuit.additions, Circuit.negations, Circuit.multiplications]
  | comp first second ihFirst ihSecond =>
      simp [differential, Tape, LinearCircuit.cost, LinearCircuit.cost_mapParams,
        Circuit.additions, Circuit.negations, Circuit.multiplications,
        ihFirst, ihSecond]
      ring_nf
  | pair left right ihLeft ihRight =>
      simp [differential, Tape, LinearCircuit.cost, LinearCircuit.cost_mapParams,
        Circuit.additions, Circuit.negations, Circuit.multiplications,
        ihLeft, ihRight]
      ring_nf
  | bundle branches ih =>
      change ∑ j, (mapParams (K := Tape (branches j))
        (L := Sigma (fun k : _ => Tape (branches k)))
        (fun t : Tape (branches j) => ⟨j, t⟩)
        (differential (branches j))).cost = _
      simp_rw [LinearCircuit.cost_mapParams]
      calc
        (∑ j, (branches j).differential.cost) =
            ∑ j, ((branches j).additions + (branches j).negations +
              3 * (branches j).multiplications) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact ih j
        _ = _ := by
          simp [Circuit.additions, Circuit.negations, Circuit.multiplications,
            Finset.sum_add_distrib, Finset.mul_sum]

theorem differential_multiplications {I O : Type} (C : Circuit I O) :
    (differential C).multiplications = 2 * C.multiplications := by
  induction C with
  | wire _ => simp [differential, LinearCircuit.multiplications, Circuit.multiplications]
  | zero => simp [differential, LinearCircuit.multiplications, Circuit.multiplications]
  | integer _ => simp [differential, LinearCircuit.multiplications, Circuit.multiplications]
  | add => simp [differential, LinearCircuit.multiplications, Circuit.multiplications]
  | neg => simp [differential, LinearCircuit.multiplications, Circuit.multiplications]
  | mul => simp [differential, multiplicationDifferential,
      LinearCircuit.multiplications, Circuit.multiplications]
  | comp first second ihFirst ihSecond =>
      simp [differential, Tape, LinearCircuit.multiplications,
        LinearCircuit.multiplications_mapParams, Circuit.multiplications,
        ihFirst, ihSecond]
      ring_nf
  | pair left right ihLeft ihRight =>
      simp [differential, Tape, LinearCircuit.multiplications,
        LinearCircuit.multiplications_mapParams, Circuit.multiplications,
        ihLeft, ihRight]
      ring_nf
  | bundle branches ih =>
      simp [differential, Tape, LinearCircuit.multiplications,
        LinearCircuit.multiplications_mapParams, Circuit.multiplications, ih,
        Finset.mul_sum]

theorem differential_eval_coeff_one {I O : Type} {R : Type*} [CommRing R]
    (C : Circuit I O) (x : I → Polynomial R) (o : O) :
    (C.eval x o).coeff 1 =
      (differential C).eval
        (tapeValues C (fun i => (x i).coeff 0))
        (fun i => (x i).coeff 1) o := by
  induction C with
  | wire select => rfl
  | zero => simp [differential]
  | integer z => exact PolynomialArithmetic.coeff_one_int z
  | add => simp [differential]
  | neg => simp [differential]
  | mul =>
      rw [Circuit.eval_mul]
      rw [PolynomialArithmetic.coeff_one_mul]
      simp [differential, multiplicationDifferential, tapeValues,
        LinearCircuit.eval]
      ring
  | comp first second ihFirst ihSecond =>
      rw [Circuit.eval_comp, ihSecond]
      simp only [differential, Tape, LinearCircuit.eval_comp]
      have hzero : first.eval (fun i => (x i).coeff 0) =
          fun j => (first.eval x j).coeff 0 := by
        funext j
        exact (eval_coeff_zero first x j).symm
      have hfirst : (differential first).eval
          (tapeValues first (fun i => (x i).coeff 0))
          (fun i => (x i).coeff 1) = fun j => (first.eval x j).coeff 1 := by
        funext j
        exact (ihFirst x j).symm
      rw [tapeValues_comp]
      rw [LinearCircuit.eval_mapParams, LinearCircuit.eval_mapParams]
      have hparamsL :
          (fun t : Tape first ⊕ Tape second =>
            match t with
            | .inl t => tapeValues first (fun i => (x i).coeff 0) t
            | .inr t => tapeValues second (first.eval (fun i => (x i).coeff 0)) t) ∘
              Sum.inl = tapeValues first (fun i => (x i).coeff 0) := by
        funext t
        rfl
      have hparamsR :
          (fun t : Tape first ⊕ Tape second =>
            match t with
            | .inl t => tapeValues first (fun i => (x i).coeff 0) t
            | .inr t => tapeValues second (first.eval (fun i => (x i).coeff 0)) t) ∘
              Sum.inr = tapeValues second (first.eval (fun i => (x i).coeff 0)) := by
        funext t
        rfl
      rw [hparamsL, hparamsR, hzero, hfirst]
  | pair left right ihLeft ihRight =>
      cases o with
      | inl o =>
          rw [Circuit.eval_pair_inl, ihLeft]
          simp only [differential, Tape, LinearCircuit.eval_pair_inl]
          rw [tapeValues_pair]
          rw [LinearCircuit.eval_mapParams]
          rfl
      | inr o =>
          rw [Circuit.eval_pair_inr, ihRight]
          simp only [differential, Tape, LinearCircuit.eval_pair_inr]
          rw [tapeValues_pair]
          rw [LinearCircuit.eval_mapParams]
          rfl
  | bundle branches ih =>
      rw [Circuit.eval_bundle, ih]
      simp only [differential, Tape, LinearCircuit.eval_bundle]
      rw [tapeValues_bundle]
      rw [LinearCircuit.eval_mapParams]
      rfl

end DivisionFree.Circuit
