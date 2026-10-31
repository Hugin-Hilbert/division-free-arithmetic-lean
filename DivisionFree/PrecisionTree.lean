import DivisionFree.Precision

/-! A concrete finite-precision splitting tree.  Each level is represented
as a list of leaf precisions; a leaf of precision zero or one is retained,
and every larger leaf is split into its two balanced children. -/

namespace DivisionFree.PrecisionTree

/-- The one-step children of a precision leaf. -/
def splitNode (q : ℕ) : List ℕ :=
  if q ≤ 1 then [q] else [q / 2, q - q / 2]

/-- Expand every leaf once, preserving the left-to-right leaf order. -/
def nextLevel (leaves : List ℕ) : List ℕ :=
  leaves.flatMap splitNode

/-- The successive levels, including the original root as level zero. -/
def levels (q : ℕ) : ℕ → List ℕ
  | 0 => [q]
  | n + 1 => nextLevel (levels q n)

private theorem splitNode_sum (q : ℕ) : (splitNode q).sum = q := by
  unfold splitNode
  split
  · simp
  · simp [DivisionFree.Precision.split_sum]

private theorem nextLevel_sum (leaves : List ℕ) :
    (nextLevel leaves).sum = leaves.sum := by
  induction leaves with
  | nil => rfl
  | cons q qs ih =>
    simp only [nextLevel, List.flatMap_cons, List.sum_append, splitNode_sum]
    simpa [nextLevel] using congrArg (fun n : ℕ => q + n) ih

/-- At every depth, the sum of all leaf precisions equals the root precision. -/
theorem level_sum (q depth : ℕ) : (levels q depth).sum = q := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    simp only [levels]
    rw [nextLevel_sum, ih]

end DivisionFree.PrecisionTree
