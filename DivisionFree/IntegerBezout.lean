import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! Explicit, computable Bézout coefficients for powers of two and three. -/

namespace DivisionFree

/-- The extended Euclidean algorithm's coefficient pair for `2^a` and `3^b`.
Both components are executable integer-valued functions. -/
def twoThreeBezout (a b : ℕ) : ℤ × ℤ :=
  (Nat.gcdA (2 ^ a) (3 ^ b), Nat.gcdB (2 ^ a) (3 ^ b))

/-- First coefficient in `twoThreeBezout`. -/
def twoThreeBezoutU (a b : ℕ) : ℤ := (twoThreeBezout a b).1

/-- Second coefficient in `twoThreeBezout`. -/
def twoThreeBezoutV (a b : ℕ) : ℤ := (twoThreeBezout a b).2

/-- The chosen coefficients satisfy Bézout's identity for every pair of
nonnegative exponents, including zero exponents. -/
theorem twoThreeBezout_identity (a b : ℕ) :
    twoThreeBezoutU a b * (2 : ℤ) ^ a +
      twoThreeBezoutV a b * (3 : ℤ) ^ b = 1 := by
  have hcop : Nat.Coprime (2 ^ a) (3 ^ b) := by
    exact Nat.Coprime.pow a b (by decide)
  have hgcd := Nat.gcd_eq_gcd_ab (2 ^ a) (3 ^ b)
  rw [hcop.gcd_eq_one] at hgcd
  simp only [Int.natCast_pow] at hgcd
  dsimp [twoThreeBezoutU, twoThreeBezoutV, twoThreeBezout]
  calc
    (Nat.gcdA (2 ^ a) (3 ^ b)) * (2 : ℤ) ^ a +
        (Nat.gcdB (2 ^ a) (3 ^ b)) * (3 : ℤ) ^ b =
      ((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) (3 ^ b) +
        ((3 ^ b : ℕ) : ℤ) * Nat.gcdB (2 ^ a) (3 ^ b) := by
      simp only [Int.natCast_pow]
      ring
    _ = 1 := hgcd.symm

/-- Remainder-normalized first coefficient. It is the least nonnegative
representative of the raw coefficient modulo `3^b`. -/
def boundedTwoThreeU (a b : ℕ) : ℤ :=
  twoThreeBezoutU a b % (3 : ℤ) ^ b

/-- Compensating second coefficient for `boundedTwoThreeU`. -/
def boundedTwoThreeV (a b : ℕ) : ℤ :=
  twoThreeBezoutV a b +
    (twoThreeBezoutU a b / (3 : ℤ) ^ b) * (2 : ℤ) ^ a

/-- Normalized coefficient names used by the full-multiplication interface. -/
abbrev twoThreeBoundedU := boundedTwoThreeU

/-- Compensating normalized coefficient used by the full-multiplication
interface. -/
abbrev twoThreeBoundedV := boundedTwoThreeV

theorem boundedTwoThree_identity (a b : ℕ) :
    boundedTwoThreeU a b * (2 : ℤ) ^ a +
      boundedTwoThreeV a b * (3 : ℤ) ^ b = 1 := by
  let u := twoThreeBezoutU a b
  let v := twoThreeBezoutV a b
  let A : ℤ := (2 : ℤ) ^ a
  let B : ℤ := (3 : ℤ) ^ b
  have hraw : u * A + v * B = 1 := by
    simpa [u, v, A, B] using twoThreeBezout_identity a b
  have heq : u % B + B * (u / B) = u := Int.emod_add_mul_ediv u B
  change (u % B) * A + (v + (u / B) * A) * B = 1
  calc
    (u % B) * A + (v + (u / B) * A) * B =
        (u % B + B * (u / B)) * A + v * B := by ring
    _ = u * A + v * B := by rw [heq]
    _ = 1 := hraw

theorem boundedTwoThreeU_nonneg (a b : ℕ) : 0 ≤ boundedTwoThreeU a b := by
  apply Int.emod_nonneg
  positivity

theorem boundedTwoThreeU_lt (a b : ℕ) :
    boundedTwoThreeU a b < (3 : ℤ) ^ b := by
  have h := Int.emod_lt (twoThreeBezoutU a b) (by positivity : (3 : ℤ) ^ b ≠ 0)
  simpa [boundedTwoThreeU, Int.natAbs_of_nonneg (by positivity : 0 ≤ (3 : ℤ) ^ b)]
    using h

theorem boundedTwoThreeV_abs_le (a b : ℕ) :
    |boundedTwoThreeV a b| ≤ (2 : ℤ) ^ a := by
  let u := boundedTwoThreeU a b
  let v := boundedTwoThreeV a b
  let A : ℤ := (2 : ℤ) ^ a
  let B : ℤ := (3 : ℤ) ^ b
  have hu0 : 0 ≤ u := by simpa [u] using boundedTwoThreeU_nonneg a b
  have huB : u < B := by simpa [u, B] using boundedTwoThreeU_lt a b
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  have hiden : u * A + v * B = 1 := by
    simpa [u, v, A, B] using boundedTwoThree_identity a b
  have hlow : -A ≤ v := by
    by_contra h
    have hv : v + A ≤ -1 := by omega
    have hmul := mul_le_mul_of_nonneg_right hv (le_of_lt hB)
    have hdelta : 0 < B - u := by omega
    have hsum : (v + A) * B = 1 + A * (B - u) := by nlinarith [hiden]
    nlinarith [mul_pos hA hdelta]
  have hhigh : v ≤ A := by
    by_contra h
    have hv : A + 1 ≤ v := by omega
    have hmul := mul_le_mul_of_nonneg_right hv (le_of_lt hB)
    have hUA : 0 ≤ u * A := mul_nonneg hu0 (le_of_lt hA)
    have hAB : 1 ≤ A * B := by nlinarith [mul_pos hA hB]
    nlinarith [hiden]
  exact abs_le.mpr ⟨hlow, hhigh⟩

theorem boundedTwoThreeU_natAbs_lt (a b : ℕ) :
    (boundedTwoThreeU a b).natAbs < 3 ^ b := by
  have hu0 := boundedTwoThreeU_nonneg a b
  have huB := boundedTwoThreeU_lt a b
  have hcast : ((boundedTwoThreeU a b).natAbs : ℤ) < (3 : ℤ) ^ b := by
    simpa [Int.natAbs_of_nonneg hu0] using huB
  exact Int.ofNat_lt.mp hcast

theorem boundedTwoThreeU_size_le (a b : ℕ) :
    (boundedTwoThreeU a b).natAbs.size ≤ 2 * b := by
  have hthree : 3 ^ b ≤ (2 ^ 2) ^ b :=
    Nat.pow_le_pow_left (by norm_num) b
  have hpow : (2 ^ 2) ^ b = 2 ^ (2 * b) := by rw [← Nat.pow_mul]
  exact (Nat.size_le).2 <| lt_of_lt_of_le (boundedTwoThreeU_natAbs_lt a b)
    (by rw [← hpow]; exact hthree)

theorem boundedTwoThreeV_natAbs_le (a b : ℕ) :
    (boundedTwoThreeV a b).natAbs ≤ 2 ^ a := by
  have habs := boundedTwoThreeV_abs_le a b
  have hcast : ((boundedTwoThreeV a b).natAbs : ℤ) ≤ (2 : ℤ) ^ a := by
    simpa [Int.natAbs_of_nonneg (abs_nonneg _)] using habs
  exact Int.ofNat_le.mp hcast

theorem boundedTwoThreeV_size_le (a b : ℕ) :
    (boundedTwoThreeV a b).natAbs.size ≤ a + 1 := by
  have hpos : 0 < 2 ^ a := Nat.pow_pos (by decide)
  have hlt : 2 ^ a < 2 ^ (a + 1) := by
    rw [Nat.pow_succ]
    nlinarith
  exact (Nat.size_le).2 <| lt_of_le_of_lt (boundedTwoThreeV_natAbs_le a b) hlt

theorem boundedTwoThree_size_sum_le (a b : ℕ) :
    (boundedTwoThreeU a b).natAbs.size +
      (boundedTwoThreeV a b).natAbs.size ≤ a + 2 * b + 1 := by
  have hu := boundedTwoThreeU_size_le a b
  have hv := boundedTwoThreeV_size_le a b
  omega

theorem twoThreeBounded_identity (a b : ℕ) :
    twoThreeBoundedU a b * (2 : ℤ) ^ a +
      twoThreeBoundedV a b * (3 : ℤ) ^ b = 1 :=
  boundedTwoThree_identity a b

theorem twoThreeBoundedU_size_le (a b : ℕ) :
    (twoThreeBoundedU a b).natAbs.size ≤ 2 * b :=
  boundedTwoThreeU_size_le a b

theorem twoThreeBoundedV_size_le (a b : ℕ) :
    (twoThreeBoundedV a b).natAbs.size ≤ a + 1 :=
  boundedTwoThreeV_size_le a b

end DivisionFree
