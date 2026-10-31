import DivisionFree.Circuit
import DivisionFree.Constants
import Mathlib.Data.Nat.Size

/-!
# Binary integer scaling circuits

Integer scalar multiplication compiled to the addition and negation syntax,
with each binary prefix computed once. No integer leaves or multiplication
gates are used.
-/

namespace DivisionFree

/-- A natural scalar circuit built by repeated doubling. -/
def nscaleBinary {I : Type} (i : I) : ℕ → Circuit I PUnit
  | 0 => .zero
  | 1 => .wire (fun _ => i)
  | n + 2 =>
      let half := nscaleBinary i ((n + 2) / 2)
      let keep := Circuit.wire (fun _ : PUnit => i)
      let collect := Circuit.pair half keep
      let doubled := Circuit.comp collect (Circuit.sum
        (.wire (fun _ : PUnit => Sum.inl PUnit.unit))
        (.wire (fun _ : PUnit => Sum.inl PUnit.unit)))
      let result := doubled
      if (n + 2) % 2 = 0 then result
      else Circuit.sum result keep
termination_by n => n
decreasing_by omega

/-- Signed integer scalar circuit, using one final negation when needed. -/
def zscaleBinary {I : Type} (i : I) (z : ℤ) : Circuit I PUnit :=
  if z < 0 then Circuit.negative (nscaleBinary i z.natAbs)
  else nscaleBinary i z.natAbs

@[simp] theorem nscaleBinary_eval {I : Type} {R : Type*} [Ring R]
    (i : I) (n : ℕ) (x : I → R) (o : PUnit) :
    (nscaleBinary i n).eval x o = (n : R) * x i := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp [nscaleBinary]
    · simp [nscaleBinary]
    · rw [nscaleBinary]
      have hh := ih ((n + 2) / 2) (by omega)
      by_cases hp : (n + 2) % 2 = 0
      · simp only [hp, if_true, Circuit.eval_comp, Circuit.eval_sum,
          Circuit.eval_wire, Circuit.eval_pair_inl]
        rw [hh]
        have hn : n + 2 = (n + 2) / 2 + (n + 2) / 2 := by omega
        conv_rhs => rw [hn]
        simp [Nat.cast_add, add_mul]
      · simp only [hp, if_false, Circuit.eval_sum, Circuit.eval_comp,
          Circuit.eval_wire, Circuit.eval_pair_inl]
        rw [hh]
        have hn : n + 2 = (n + 2) / 2 + (n + 2) / 2 + 1 := by omega
        conv_rhs => rw [hn]
        simp [Nat.cast_add, add_mul]

private theorem size_half_add_one (n : ℕ) (hn : 0 < n) :
    (n / 2).size + 1 = n.size := by
  have hb : Nat.bit (decide (n % 2 = 1)) (n / 2) = n := by
    by_cases hp : n % 2 = 1 <;> simp [hp, Nat.bit_val] <;> omega
  have h := Nat.size_bit (b := decide (n % 2 = 1)) (n := n / 2)
    (by rw [hb]; omega)
  simpa only [hb, Nat.succ_eq_add_one] using h.symm

theorem nscaleBinary_cost_le {I : Type} (i : I) (n : ℕ) :
    (nscaleBinary i n).cost ≤ 2 * n.size := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp [nscaleBinary]
    · simp [nscaleBinary]
    · change (nscaleBinary i (n + 2)).cost ≤ 2 * (n + 2).size
      rw [nscaleBinary]
      have hh := ih ((n + 2) / 2) (by omega)
      have hs := size_half_add_one (n + 2) (by omega)
      split <;> simp only [Circuit.comp_cost, Circuit.pair_cost, Circuit.wire_cost,
        Circuit.sum_cost] <;> omega

@[simp] theorem nscaleBinary_multiplications {I : Type} (i : I) (n : ℕ) :
    (nscaleBinary i n).multiplications = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp [nscaleBinary]
    · simp [nscaleBinary]
    · rw [nscaleBinary]
      have hh := ih ((n + 2) / 2) (by omega)
      split <;> simp only [Circuit.comp_multiplications, Circuit.pair_multiplications,
        Circuit.wire_multiplications, Circuit.sum_multiplications, hh, add_zero]

@[simp] theorem nscaleBinary_constantBits {I : Type} (i : I) (n : ℕ) :
    (nscaleBinary i n).constantBits = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp [nscaleBinary, Circuit.constantBits]
    · simp [nscaleBinary, Circuit.constantBits]
    · rw [nscaleBinary]
      have hh := ih ((n + 2) / 2) (by omega)
      split <;> simp only [Circuit.sum, Circuit.constantBits, hh, add_zero]

@[simp] theorem zscaleBinary_eval {I : Type} {R : Type*} [Ring R]
    (i : I) (z : ℤ) (x : I → R) (o : PUnit) :
    (zscaleBinary i z).eval x o = (z : R) * x i := by
  cases z with
  | ofNat n =>
    have h : ¬ (n : ℤ) < 0 := not_lt.mpr (Int.natCast_nonneg n)
    simp only [zscaleBinary, Int.ofNat_eq_natCast, if_neg h, Int.natAbs_natCast,
      nscaleBinary_eval, Int.cast_natCast]
  | negSucc n =>
    have h : Int.negSucc n < 0 := by omega
    simp only [zscaleBinary, if_pos h, Circuit.eval_negative, nscaleBinary_eval,
      Int.natAbs_negSucc, Int.cast_negSucc, Nat.cast_succ]
    simp only [add_mul, one_mul, neg_add_rev]
    simp only [neg_mul, one_mul]

theorem zscaleBinary_cost_le {I : Type} (i : I) (z : ℤ) :
    (zscaleBinary i z).cost ≤ 2 * z.natAbs.size + 1 := by
  have h := nscaleBinary_cost_le i z.natAbs
  unfold zscaleBinary
  split_ifs
  · rw [Circuit.negative_cost]; omega
  · omega

@[simp] theorem zscaleBinary_multiplications {I : Type} (i : I) (z : ℤ) :
    (zscaleBinary i z).multiplications = 0 := by
  unfold zscaleBinary
  split_ifs <;> simp

@[simp] theorem zscaleBinary_constantBits {I : Type} (i : I) (z : ℤ) :
    (zscaleBinary i z).constantBits = 0 := by
  unfold zscaleBinary
  split_ifs <;> simp [Circuit.negative, Circuit.constantBits]

end DivisionFree
