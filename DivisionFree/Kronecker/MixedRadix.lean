import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! Self-contained mixed-radix encoding for full-range Kronecker products.
The least-significant digit is stored first; radix one is allowed. -/

namespace DivisionFree.Kronecker

/-- The number of representable indices in a mixed-radix box. -/
def capacity : List ℕ → ℕ
  | [] => 1
  | d :: ds => d * capacity ds

/-- Digits of a natural number, least-significant coordinate first. -/
def digits : List ℕ → ℕ → List ℕ
  | [], _ => []
  | d :: ds, e => e % d :: digits ds (e / d)

/-- Encode a digit list with the specified radices. -/
def encode : List ℕ → List ℕ → ℕ
  | d :: ds, a :: as => a + d * encode ds as
  | _, _ => 0

/-- A digit vector whose coordinates lie in their corresponding radix. -/
def Valid : List ℕ → List ℕ → Prop
  | [], [] => True
  | d :: ds, a :: as => a < d ∧ Valid ds as
  | _, _ => False

theorem digits_length (ds : List ℕ) (e : ℕ) :
    (digits ds e).length = ds.length := by
  induction ds generalizing e with
  | nil => rfl
  | cons d ds ih => simp [digits, ih]

theorem encode_digits (ds : List ℕ) (e : ℕ) (he : e < capacity ds) :
    encode ds (digits ds e) = e := by
  induction ds generalizing e with
  | nil => simp_all [capacity, encode]
  | cons d ds ih =>
      have hd : 0 < d := by
        by_contra h
        simp [capacity, Nat.eq_zero_of_not_pos h] at he
      have hquot : e / d < capacity ds := by
        exact (Nat.div_lt_iff_lt_mul hd).2 (by simpa [capacity, Nat.mul_comm] using he)
      simp only [digits, encode, ih _ hquot]
      exact Nat.mod_add_div e d

theorem valid_digits (ds : List ℕ) (e : ℕ) (he : e < capacity ds) :
    Valid ds (digits ds e) := by
  induction ds generalizing e with
  | nil => trivial
  | cons d ds ih =>
      have hd : 0 < d := by
        by_contra h
        simp [capacity, Nat.eq_zero_of_not_pos h] at he
      exact ⟨Nat.mod_lt e hd,
        ih _ ((Nat.div_lt_iff_lt_mul hd).2 (by simpa [capacity, Nat.mul_comm] using he))⟩

theorem digits_encode (ds as : List ℕ) (h : Valid ds as) :
    digits ds (encode ds as) = as := by
  induction ds generalizing as with
  | nil => cases as <;> simp_all [Valid, digits]
  | cons d ds ih =>
      cases as with
      | nil => simp [Valid] at h
      | cons a as =>
          obtain ⟨ha, has⟩ := h
          have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le a) ha
          simp only [digits, encode, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha,
            Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt ha, zero_add, ih as has]

theorem valid_length_eq (ds as : List ℕ) (h : Valid ds as) :
    as.length = ds.length := by
  induction ds generalizing as with
  | nil => cases as <;> simp_all [Valid]
  | cons d ds ih =>
      cases as with
      | nil => simp [Valid] at h
      | cons a as =>
          simp only [Valid] at h
          simpa using congrArg Nat.succ (ih as h.2)

theorem encode_lt_capacity (ds as : List ℕ) (h : Valid ds as) :
    encode ds as < capacity ds := by
  induction ds generalizing as with
  | nil => cases as <;> simp_all [Valid, encode, capacity]
  | cons d ds ih =>
      cases as with
      | nil => simp [Valid] at h
      | cons a as =>
          obtain ⟨ha, has⟩ := h
          have hi := ih as has
          simp only [encode, capacity]
          nlinarith

theorem encode_injective_on_valid (ds as bs : List ℕ)
    (ha : Valid ds as) (hb : Valid ds bs) (h : encode ds as = encode ds bs) :
    as = bs := by
  rw [← digits_encode ds as ha, ← digits_encode ds bs hb, h]

/-- Coordinatewise addition of exponent vectors. -/
def digitAdd : List ℕ → List ℕ → List ℕ
  | a :: as, b :: bs => (a + b) :: digitAdd as bs
  | _, _ => []

theorem encode_digitAdd (ds a b : List ℕ)
    (ha : a.length = ds.length) (hb : b.length = ds.length) :
    encode ds (digitAdd a b) = encode ds a + encode ds b := by
  induction ds generalizing a b with
  | nil => cases a <;> cases b <;> simp [encode] at *
  | cons d ds ih =>
      cases a with
      | nil => simp at ha
      | cons a as =>
          cases b with
          | nil => simp at hb
          | cons b bs =>
              have hla : as.length = ds.length := by simp at ha; omega
              have hlb : bs.length = ds.length := by simp at hb; omega
              simp only [digitAdd, encode]
              rw [ih as bs hla hlb]
              ring

/-- Pairwise sums of two vectors in a box fit the full convolution box
whose side lengths are `2 * side - 1`. -/
theorem valid_digitAdd_double_sub_one (ds a b : List ℕ)
    (ha : Valid ds a) (hb : Valid ds b) :
    Valid (ds.map (fun d => 2 * d - 1)) (digitAdd a b) := by
  induction ds generalizing a b with
  | nil => cases a <;> cases b <;> simp_all [Valid, digitAdd]
  | cons d ds ih =>
      cases a with
      | nil => cases ha
      | cons a as =>
          cases b with
          | nil => cases hb
          | cons b bs =>
              simp only [Valid, List.map_cons, digitAdd]
              exact ⟨by have h₁ := ha.1; have h₂ := hb.1; omega,
                ih as bs ha.2 hb.2⟩

/-- Equality of full mixed-radix exponents cannot alias two distinct
coordinatewise product indices when every product coordinate fits its full
`2*s-1` range. -/
theorem fullProduct_no_alias (ds a b c d : List ℕ)
    (ha : Valid ds a) (hb : Valid ds b) (hc : Valid ds c) (hd : Valid ds d)
    (heq : encode (ds.map (fun n => 2 * n - 1)) (digitAdd a b) =
      encode (ds.map (fun n => 2 * n - 1)) (digitAdd c d)) :
    digitAdd a b = digitAdd c d := by
  apply encode_injective_on_valid (ds.map (fun n => 2 * n - 1))
  · exact valid_digitAdd_double_sub_one ds a b ha hb
  · exact valid_digitAdd_double_sub_one ds c d hc hd
  · exact heq

/-- The encoded exponent of a pair is the sum of its independently encoded
input exponents. -/
theorem fullProduct_encode_pair (ds a b : List ℕ)
    (ha : Valid ds a) (hb : Valid ds b) :
    encode ds (digitAdd a b) = encode ds a + encode ds b :=
  encode_digitAdd ds a b (valid_length_eq ds a ha) (valid_length_eq ds b hb)

end DivisionFree.Kronecker
