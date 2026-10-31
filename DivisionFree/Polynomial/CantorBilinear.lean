import DivisionFree.Circuit.BilinearCircuit
import DivisionFree.Polynomial.CantorPreparedLinear

/-! A separated bilinear implementation of the public Cantor--Kaltofen
multiplier, including actual preparation and the original asymptotic split. -/

namespace DivisionFree.PolynomialArithmetic

open Circuit

universe u

/-- A concrete separated linear--product--linear factorization of the
existing multiplier; its scalar preparation is also an actual circuit. -/
theorem fastFullMultiplier_bilinear_decomposition (n : ℕ)
    {R : Type u} [CommRing R] (a b : Fin n → R) :
    let C := (fastFullMultiplier.{u} n).splitCircuit
    let params := (Circuit.bilinearPreparation.{u} C).eval (fun _ => (0 : R))
    (Circuit.bilinearFinish.{u} C).eval params
      (fun t => (Circuit.bilinearLeft.{u} C).eval params a t *
        (Circuit.bilinearRight.{u} C).eval params b t) =
      (fastFullMultiplier.{u} n).circuit.eval (fun z => if z.1 then b z.2 else a z.2) := by
  dsimp only
  funext j
  rw [Circuit.bilinearFinish_eval, Circuit.coeff11_of_bihomogeneous _
    (fastFullMultiplier_splitCircuit_bihomogeneous n)]
  exact congrFun ((fastFullMultiplier.{u} n).splitCircuit_eval a b) j

/-- Prepare constants once, apply separate left and right linear circuits,
multiply matching coordinates, and apply the final linear circuit. -/
noncomputable def cantorBilinearCircuit (n : ℕ) :
    Circuit (Fin n ⊕ Fin n) (Fin (2 * n)) :=
  Circuit.bilinearCircuit.{u} (fastFullMultiplier.{u} n).splitCircuit

theorem cantorBilinearCircuit_correct (n : ℕ)
    {R : Type u} [CommRing R] (a b : Fin n → R) :
    (cantorBilinearCircuit.{u} n).eval (Sum.elim a b) =
      (fastFullMultiplier.{u} n).circuit.eval (fun z => if z.1 then b z.2 else a z.2) := by
  rw [cantorBilinearCircuit, Circuit.bilinearCircuit_correct
    (fastFullMultiplier.{u} n).splitCircuit (fastFullMultiplier_splitCircuit_bihomogeneous n)]
  exact (fastFullMultiplier.{u} n).splitCircuit_eval a b

/-- Number of products in the single layer that combines the two input blocks. -/
theorem cantorBilinearCircuit_rank_le (n : ℕ) :
    Fintype.card (fastFullMultiplier.{u} n).splitCircuit.Tape ≤
      780 * n * (Nat.log 2 (2 * n) + 1) := by
  rw [Circuit.tape_card, FullMultiplier.splitCircuit_multiplications]
  have hm := fastFullMultiplier_multiplications_le.{u} n
  nlinarith

theorem cantorBilinearCircuit_cost (n : ℕ) :
    (cantorBilinearCircuit.{u} n).cost =
      4 * (fastFullMultiplier.{u} n).cost +
        10 * (fastFullMultiplier.{u} n).circuit.multiplications := by
  rw [cantorBilinearCircuit, Circuit.bilinearCircuit_cost,
    FullMultiplier.splitCircuit_cost, FullMultiplier.splitCircuit_multiplications]

theorem cantorBilinearCircuit_multiplications (n : ℕ) :
    (cantorBilinearCircuit.{u} n).multiplications =
      9 * (fastFullMultiplier.{u} n).circuit.multiplications := by
  rw [cantorBilinearCircuit, Circuit.bilinearCircuit_multiplications,
    FullMultiplier.splitCircuit_multiplications]

theorem cantorBilinearCircuit_constantBits (n : ℕ) :
    (cantorBilinearCircuit.{u} n).constantBits =
      (fastFullMultiplier.{u} n).circuit.constantBits := by
  rw [cantorBilinearCircuit, Circuit.bilinearCircuit_constantBits,
    FullMultiplier.splitCircuit_constantBits]

theorem cantorBilinearCircuit_cost_le (n : ℕ) :
    (cantorBilinearCircuit.{u} n).cost ≤
      4872 * n * (Nat.log 2 (2 * n) + 1) *
        (Nat.log 2 (Nat.log 2 (2 * n) + 1) + 2) := by
  rw [cantorBilinearCircuit_cost]
  have hc := fastFullMultiplier_cantor_log_cost_le.{u} n
  have hm := fastFullMultiplier_multiplications_le.{u} n
  have hscale := cantor_log_scale_three n
  nlinarith

theorem cantorBilinearCircuit_multiplications_le (n : ℕ) :
    (cantorBilinearCircuit.{u} n).multiplications ≤
      3510 * n * (Nat.log 2 (2 * n) + 1) := by
  rw [cantorBilinearCircuit_multiplications]
  have hm := fastFullMultiplier_multiplications_le.{u} n
  nlinarith

theorem cantorBilinearCircuit_constantBits_le (n : ℕ) :
    (cantorBilinearCircuit.{u} n).constantBits ≤
      30 * n * (Nat.log 2 (2 * n) + 1) := by
  rw [cantorBilinearCircuit_constantBits]
  exact fastFullMultiplier_constantBits_le n

/-- The separated circuit implements the same full-product interface,
including the highest output slots and the zero-length case. -/
noncomputable def bilinearFastFullMultiplier (n : ℕ) : FullMultiplier.{u} n where
  circuit := .comp
    (.wire (Sum.elim (fun i => (false, i)) (fun i => (true, i))))
    (cantorBilinearCircuit.{u} n)
  correct := by
    intro R _ input
    simp only [Circuit.eval_comp_function, Circuit.eval_wire_function]
    have hin : (fun z => input (Sum.elim (fun i => (false, i)) (fun i => (true, i)) z)) =
        Sum.elim (fun i => input (false, i)) (fun i => input (true, i)) := by
      funext z
      cases z <;> rfl
    rw [hin, cantorBilinearCircuit_correct]
    have hinput : (fun z : Bool × Fin n =>
        if z.1 then input (true, z.2) else input (false, z.2)) = input := by
      funext z
      rcases z with ⟨b, i⟩
      cases b <;> rfl
    rw [hinput]
    exact (fastFullMultiplier.{u} n).correct R input

theorem bilinearFastFullMultiplier_cost_le (n : ℕ) :
    (bilinearFastFullMultiplier.{u} n).cost ≤
      4872 * n * (Nat.log 2 (2 * n) + 1) *
        (Nat.log 2 (Nat.log 2 (2 * n) + 1) + 2) := by
  simpa only [bilinearFastFullMultiplier, FullMultiplier.cost, Circuit.comp_cost,
    Circuit.wire_cost, Nat.zero_add] using cantorBilinearCircuit_cost_le.{u} n

theorem bilinearFastFullMultiplier_multiplications_le (n : ℕ) :
    (bilinearFastFullMultiplier.{u} n).circuit.multiplications ≤
      3510 * n * (Nat.log 2 (2 * n) + 1) := by
  simpa only [bilinearFastFullMultiplier, Circuit.comp_multiplications,
    Circuit.wire_multiplications, Nat.zero_add] using
    cantorBilinearCircuit_multiplications_le.{u} n

theorem bilinearFastFullMultiplier_additions_negations_le (n : ℕ) :
    (bilinearFastFullMultiplier.{u} n).circuit.additions +
      (bilinearFastFullMultiplier.{u} n).circuit.negations ≤
      4872 * n * (Nat.log 2 (2 * n) + 1) *
        (Nat.log 2 (Nat.log 2 (2 * n) + 1) + 2) := by
  have h := bilinearFastFullMultiplier_cost_le.{u} n
  unfold FullMultiplier.cost Circuit.cost at h
  omega

theorem bilinearFastFullMultiplier_constantBits_le (n : ℕ) :
    (bilinearFastFullMultiplier.{u} n).circuit.constantBits ≤
      30 * n * (Nat.log 2 (2 * n) + 1) := by
  simpa only [bilinearFastFullMultiplier, Circuit.comp_constantBits,
    Circuit.constantBits, Nat.zero_add] using cantorBilinearCircuit_constantBits_le.{u} n

end DivisionFree.PolynomialArithmetic
