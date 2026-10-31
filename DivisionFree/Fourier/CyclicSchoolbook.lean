import DivisionFree.Fourier.Basic
import DivisionFree.Polynomial.Schoolbook
import DivisionFree.Constants

/-! A quadratic circuit for cyclic convolution, used as a small-size base case. -/

namespace DivisionFree.Fourier

open DivisionFree
open scoped BigOperators

private def cyclicProductTerm (M : ℕ) (k j : ZMod M) :
    Circuit (Bool × ZMod M) PUnit :=
  .comp (.wire (fun b : Bool => if b then (true, k - j) else (false, j))) .mul


private theorem sumList_constantBits {I : Type} (ps : List (Circuit I PUnit))
    (h : ∀ p ∈ ps, p.constantBits = 0) :
    (Circuit.sumList ps).constantBits = 0 := by
  induction ps with
  | nil => simp [Circuit.sumList, Circuit.constantBits]
  | cons p ps ih =>
      have hp : p.constantBits = 0 := h p (by simp)
      have hps : ∀ q ∈ ps, q.constantBits = 0 := by
        intro q hq
        exact h q (by simp [hq])
      simp [Circuit.sumList, Circuit.sum, Circuit.constantBits, hp, ih hps]

/-- Direct cyclic convolution by summing all `M` pairwise products at each
output position. -/
noncomputable def cyclicSchoolbook (M : ℕ) [NeZero M] :
    Circuit (Bool × ZMod M) (ZMod M) :=
  .comp (.bundle fun k => Circuit.sumList
    (Finset.univ.toList.map (cyclicProductTerm M k)))
    (.wire fun k => (k, PUnit.unit))

theorem cyclicProductTerm_cost (M : ℕ) (k j : ZMod M) :
    (cyclicProductTerm M k j).cost = 1 := by
  simp [cyclicProductTerm]

theorem cyclicSchoolbook_eval {R : Type*} [CommRing R]
    (M : ℕ) [NeZero M] (x : Bool × ZMod M → R) (k : ZMod M) :
    (cyclicSchoolbook M).eval x k =
      ∑ j : ZMod M, x (false, j) * x (true, k - j) := by
  classical
  simp [cyclicSchoolbook, cyclicProductTerm, Circuit.sumList_eval,
    List.map_map]

theorem cyclicSchoolbook_eq_convolution {R : Type*} [CommRing R]
    (M : ℕ) [NeZero M] (x : Bool × ZMod M → R) (k : ZMod M) :
    (cyclicSchoolbook M).eval x k =
      convolution (fun j => x (false, j)) (fun j => x (true, j)) k := by
  rw [cyclicSchoolbook_eval]
  rfl

theorem cyclicSchoolbook_cost (M : ℕ) [NeZero M] :
    (cyclicSchoolbook M).cost = 2 * M ^ 2 := by
  classical
  simp [cyclicSchoolbook, cyclicProductTerm, Circuit.sumList_cost,
    List.map_map, ZMod.card]
  ring

theorem cyclicSchoolbook_constantBits (M : ℕ) [NeZero M] :
    (cyclicSchoolbook M).constantBits = 0 := by
  classical
  simp only [cyclicSchoolbook, Circuit.comp_constantBits, Circuit.constantBits]
  apply Finset.sum_eq_zero
  intro k hk
  apply sumList_constantBits
  intro p hp
  rcases List.mem_map.mp hp with ⟨j, hj, rfl⟩
  simp [cyclicProductTerm, Circuit.constantBits]

private theorem sumList_multiplications_eq_length {I : Type}
    (ps : List (Circuit I PUnit)) (h : ∀ p ∈ ps, p.multiplications = 1) :
    (Circuit.sumList ps).multiplications = ps.length := by
  induction ps with
  | nil => simp [Circuit.sumList]
  | cons p ps ih =>
      have hp := h p (by simp)
      have hps : ∀ q ∈ ps, q.multiplications = 1 := by
        intro q hq
        exact h q (by simp [hq])
      simp [Circuit.sumList, hp, ih hps]
      omega

theorem cyclicSchoolbook_multiplications_eq (M : ℕ) [NeZero M] :
    (cyclicSchoolbook M).multiplications = M ^ 2 := by
  classical
  unfold cyclicSchoolbook
  change (∑ k : ZMod M,
      (Circuit.sumList (Finset.univ.toList.map (cyclicProductTerm M k))).multiplications) = M ^ 2
  calc
    (∑ k : ZMod M,
        (Circuit.sumList (Finset.univ.toList.map (cyclicProductTerm M k))).multiplications) =
        ∑ _k : ZMod M, M := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [sumList_multiplications_eq_length]
          · simp [ZMod.card]
          · intro p hp
            rcases List.mem_map.mp hp with ⟨j, hj, rfl⟩
            simp [cyclicProductTerm]
    _ = M ^ 2 := by simp [ZMod.card, pow_two]


end DivisionFree.Fourier
