import DivisionFree.Fourier.Cyclotomic
import DivisionFree.Fourier.BlockReduction

/-! Ternary root identities in arbitrary cyclotomic coefficient rings. -/

namespace DivisionFree.Fourier

/-- The distinguished nontrivial ternary root in a `3^q` cyclotomic ring
satisfies the quadratic relation, including over the zero ring. -/
theorem ternaryCyclotomicRoot_relation {R : Type*} [CommRing R]
    (q : ℕ) (hq : 0 < q) :
    1 + cyclotomicCharacter R (3 ^ q) ((3 ^ (q - 1) : ℕ) : ZMod (3 ^ q)) +
      (cyclotomicCharacter R (3 ^ q) ((3 ^ (q - 1) : ℕ) : ZMod (3 ^ q))) ^ 2 = 0 := by
  letI : NeZero (3 ^ q) := ⟨by positivity⟩
  have hqexp : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  have hgeom := cyclotomicRoot_geom_sum (R := R) 3 (q - 1) Nat.prime_three
  rw [hqexp] at hgeom
  have hgeom' :
      1 + cyclotomicRoot R (3 ^ q) ^ (3 ^ (q - 1)) +
        (cyclotomicRoot R (3 ^ q) ^ (3 ^ (q - 1))) ^ 2 = 0 := by
    simpa [Fin.sum_univ_three, pow_mul] using hgeom
  have hchar : cyclotomicCharacter R (3 ^ q)
      ((3 ^ (q - 1) : ℕ) : ZMod (3 ^ q)) =
      cyclotomicRoot R (3 ^ q) ^ (3 ^ (q - 1)) := by
    unfold cyclotomicCharacter
    rw [AddChar.zmodChar_apply']
  calc
    1 + cyclotomicCharacter R (3 ^ q)
          ((3 ^ (q - 1) : ℕ) : ZMod (3 ^ q)) +
        (cyclotomicCharacter R (3 ^ q)
          ((3 ^ (q - 1) : ℕ) : ZMod (3 ^ q))) ^ 2 =
      1 + cyclotomicRoot R (3 ^ q) ^ (3 ^ (q - 1)) +
        (cyclotomicRoot R (3 ^ q) ^ (3 ^ (q - 1))) ^ 2 := by rw [hchar]
    _ = 0 := hgeom'

/-- Multiplication by the radix power transports the chosen smaller ternary
root index to the base-`3` cyclotomic index. -/
theorem ternaryRootIndex_mul {q r : ℕ} (hrq : r + 1 ≤ q) :
    3 ^ r • ((3 ^ (q - (r + 1)) : ℕ) : ZMod (3 ^ q)) =
      ((3 ^ (q - 1) : ℕ) : ZMod (3 ^ q)) := by
  calc
    3 ^ r • ((3 ^ (q - (r + 1)) : ℕ) : ZMod (3 ^ q)) =
        ((3 ^ r * 3 ^ (q - (r + 1)) : ℕ) : ZMod (3 ^ q)) := by
          rw [nsmul_eq_mul, ← Nat.cast_mul]
    _ = ((3 ^ (r + (q - (r + 1))) : ℕ) : ZMod (3 ^ q)) := by
          rw [← pow_add]
    _ = ((3 ^ (q - 1) : ℕ) : ZMod (3 ^ q)) := by
          have hexp : r + (q - (r + 1)) = q - 1 := by omega
          rw [hexp]

end DivisionFree.Fourier
