import DivisionFree.PrecisionTree
import Mathlib.Tactic

/-! Cost accounting for the balanced precision tree. -/

namespace DivisionFree.PrecisionTree

/-- A leaf pays for its precision; each internal node pays a linear toll. -/
def costRecurrence (base toll q : ℕ) : ℕ :=
  if q ≤ 1 then base * q
  else costRecurrence base toll (q / 2) +
      costRecurrence base toll (q - q / 2) + toll * q
termination_by q
decreasing_by
  all_goals
    have hq : 2 ≤ q := by omega
    have hs := DivisionFree.Precision.split_bounds q hq
    omega

/-- Both balanced children have strictly smaller binary ceiling logarithm.
This is the height measure for the complete splitting tree. -/
theorem split_clog_lt (q : ℕ) (hq : 2 ≤ q) :
    Nat.clog 2 (q / 2) < Nat.clog 2 q ∧
      Nat.clog 2 (q - q / 2) < Nat.clog 2 q := by
  let d := Nat.clog 2 q
  have hdpos : 1 ≤ d := by
    dsimp [d]
    exact Nat.clog_pos (by decide) (by omega)
  have hqpow : q ≤ 2 ^ d := by
    dsimp [d]
    exact Nat.le_pow_clog (by decide) q
  have hpow : 2 ^ d = 2 ^ (d - 1) * 2 := by
    calc
      2 ^ d = 2 ^ (d - 1 + 1) := by congr 1; omega
      _ = 2 ^ (d - 1) * 2 := by rw [Nat.pow_succ]
  have hdiv : q = 2 * (q / 2) + q % 2 := by omega
  have hmod : q % 2 ≤ 1 := by omega
  have hleft : q / 2 ≤ 2 ^ (d - 1) := by omega
  have hright : q - q / 2 ≤ 2 ^ (d - 1) := by omega
  have hlc : Nat.clog 2 (q / 2) ≤ d - 1 :=
    Nat.clog_le_of_le_pow hleft
  have hrc : Nat.clog 2 (q - q / 2) ≤ d - 1 :=
    Nat.clog_le_of_le_pow hright
  constructor <;> dsimp [d] at * <;> omega

/-- The exact linear toll paid by one complete precision level. -/
theorem level_linear_toll (q depth toll : ℕ) :
    ((levels q depth).map (fun x => toll * x)).sum = toll * q := by
  have mapSum (xs : List ℕ) : (xs.map (fun x => toll * x)).sum = toll * xs.sum := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [mapSum, level_sum]

/-- The total linear toll over the first `depth` complete levels. -/
def levelTollCost (q depth toll : ℕ) : ℕ :=
  ∑ d ∈ Finset.range depth, ((levels q d).map (fun x => toll * x)).sum

theorem levelTollCost_eq (q depth toll : ℕ) :
    levelTollCost q depth toll = depth * toll * q := by
  simp [levelTollCost, level_linear_toll, Nat.mul_assoc, Finset.sum_const]

private theorem nextLevel_eq_of_le_one (leaves : List ℕ)
    (h : ∀ q ∈ leaves, q ≤ 1) : nextLevel leaves = leaves := by
  induction leaves with
  | nil => rfl
  | cons q qs ih =>
      have hq := h q (by simp)
      have hqs : ∀ r ∈ qs, r ≤ 1 := by
        intro r hr
        exact h r (by simp [hr])
      simp only [nextLevel, List.flatMap_cons]
      rw [splitNode, if_pos hq]
      change [q] ++ nextLevel qs = q :: qs
      rw [ih hqs]
      rfl

private theorem nextLevel_append (xs ys : List ℕ) :
    nextLevel (xs ++ ys) = nextLevel xs ++ nextLevel ys := by
  simp [nextLevel, List.flatMap_append]

/-- After the first split, each later level is the concatenation of the
corresponding levels of the two children. -/
theorem levels_split (q : ℕ) (hq : 2 ≤ q) (depth : ℕ) :
    levels q (depth + 1) =
      levels (q / 2) depth ++ levels (q - q / 2) depth := by
  induction depth with
  | zero =>
      have hnot : ¬ q ≤ 1 := by omega
      simp [levels, nextLevel, splitNode, hnot]
  | succ depth ih =>
      change nextLevel (levels q (depth + 1)) =
        nextLevel (levels (q / 2) depth) ++ nextLevel (levels (q - q / 2) depth)
      rw [ih, nextLevel_append]

/-- Once all leaves are at most one, the remaining levels repeat unchanged. -/
theorem levels_le_one_of {q start finish : ℕ}
    (hstart : ∀ x ∈ levels q start, x ≤ 1) (hdepth : start ≤ finish) :
    ∀ x ∈ levels q finish, x ≤ 1 := by
  induction finish, hdepth using Nat.le_induction with
  | base => exact hstart
  | succ finish hle ih =>
      have hfix := nextLevel_eq_of_le_one (levels q finish) ih
      simpa [levels, hfix] using ih

/-- The complete balanced splitting tree has no non-leaf precision after
`Nat.clog 2 q` levels. -/
theorem levels_le_one_at_clog (q : ℕ) :
    ∀ x ∈ levels q (Nat.clog 2 q), x ≤ 1 := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
      by_cases hleaf : q ≤ 1
      · have hclog : Nat.clog 2 q = 0 := Nat.clog_of_right_le_one hleaf 2
        simp [hclog, levels, hleaf]
      · have hq : 2 ≤ q := by omega
        have hcpos : 0 < Nat.clog 2 q :=
          Nat.clog_pos (b := 2) (n := q) (by omega) (by omega)
        have hdepth : 1 ≤ Nat.clog 2 q := by omega
        have hsplit := split_clog_lt q hq
        have hleft := ih (q / 2) (by omega)
        have hright := ih (q - q / 2) (by omega)
        have hleftdepth : Nat.clog 2 (q / 2) ≤ Nat.clog 2 q - 1 := by omega
        have hrightdepth : Nat.clog 2 (q - q / 2) ≤ Nat.clog 2 q - 1 := by omega
        have hleft' := levels_le_one_of hleft hleftdepth
        have hright' := levels_le_one_of hright hrightdepth
        have hd : Nat.clog 2 q = (Nat.clog 2 q - 1) + 1 := by omega
        have hlevel : levels q (Nat.clog 2 q) =
            levels (q / 2) (Nat.clog 2 q - 1) ++
              levels (q - q / 2) (Nat.clog 2 q - 1) := by
          rw [hd]
          exact levels_split q hq (Nat.clog 2 q - 1)
        intro x hx
        rw [hlevel] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hleft' x hx
        · exact hright' x hx

/-- Number of split levels on any root-to-leaf path, expressed as a binary
ceiling logarithm. -/
def treeDepth (q : ℕ) : ℕ := Nat.clog 2 q

theorem completeTree_leaves (q : ℕ) :
    ∀ x ∈ levels q (treeDepth q), x ≤ 1 := by
  simpa [treeDepth] using levels_le_one_at_clog q

/-- A full level has total precision exactly q, so its linear toll is exactly
`toll * q`. -/
theorem fullLevelToll_eq (q depth toll : ℕ) :
    ((levels q depth).map (fun x => toll * x)).sum = toll * q :=
  level_linear_toll q depth toll

/-- Charging every node on each of the `treeDepth q` levels upper-bounds the
actual internal-node toll. Its exact value is explicit. -/
theorem completeTreeToll_eq (q toll : ℕ) :
    levelTollCost q (treeDepth q) toll = treeDepth q * toll * q := by
  simpa [treeDepth] using levelTollCost_eq q (Nat.clog 2 q) toll

/-- The complete balanced tree costs at most its leaf budget plus one
linear-precision toll per level. This includes precision zero. -/
theorem costRecurrence_le (base toll q : ℕ) :
    costRecurrence base toll q ≤ q * (base + toll * Nat.clog 2 q) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
      by_cases hleaf : q ≤ 1
      · have hclog : Nat.clog 2 q = 0 := Nat.clog_of_right_le_one hleaf 2
        simp [costRecurrence, hleaf, hclog, Nat.mul_comm]
      · have hq : 2 ≤ q := by omega
        have hsplit := split_clog_lt q hq
        have hleft : q / 2 < q := by omega
        have hright : q - q / 2 < q := by omega
        have ihleft := ih (q / 2) hleft
        have ihright := ih (q - q / 2) hright
        rw [costRecurrence, if_neg hleaf]
        have hsum := DivisionFree.Precision.split_sum q
        have hleftlog : Nat.clog 2 (q / 2) ≤ Nat.clog 2 q - 1 := by
          have h := hsplit.1
          omega
        have hrightlog : Nat.clog 2 (q - q / 2) ≤ Nat.clog 2 q - 1 := by
          have h := hsplit.2
          omega
        calc
          costRecurrence base toll (q / 2) +
              costRecurrence base toll (q - q / 2) + toll * q ≤
              (q / 2) * (base + toll * (Nat.clog 2 q - 1)) +
              (q - q / 2) * (base + toll * (Nat.clog 2 q - 1)) + toll * q := by
            have hl := ihleft.trans (Nat.mul_le_mul_left (q / 2)
              (Nat.add_le_add_left (Nat.mul_le_mul_left toll hleftlog) base))
            have hr := ihright.trans (Nat.mul_le_mul_left (q - q / 2)
              (Nat.add_le_add_left (Nat.mul_le_mul_left toll hrightlog) base))
            exact Nat.add_le_add_right (Nat.add_le_add hl hr) _
          _ = q * (base + toll * Nat.clog 2 q) := by
            rw [← Nat.add_mul, hsum]
            have hd : Nat.clog 2 q - 1 + 1 = Nat.clog 2 q := by omega
            calc
              _ = q * (base + toll * (Nat.clog 2 q - 1 + 1)) := by ring
              _ = _ := by rw [hd]

/-- A logarithmic version of the balanced-tree cost estimate. -/
theorem costRecurrence_log_le (base toll q : ℕ) :
    costRecurrence base toll q ≤
      q * (base + toll * (Nat.log 2 q + 1)) := by
  have hpow : q ≤ 2 ^ (Nat.log 2 q + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by omega) q
    omega
  have hclog : Nat.clog 2 q ≤ Nat.log 2 q + 1 :=
    Nat.clog_le_of_le_pow hpow
  calc
    costRecurrence base toll q ≤ q * (base + toll * Nat.clog 2 q) :=
      costRecurrence_le base toll q
    _ ≤ q * (base + toll * (Nat.log 2 q + 1)) := by
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add_left (Nat.mul_le_mul_left toll hclog) base

end DivisionFree.PrecisionTree
