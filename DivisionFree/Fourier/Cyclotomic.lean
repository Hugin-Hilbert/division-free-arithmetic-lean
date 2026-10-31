import DivisionFree.Fourier.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Algebra.CharP.Algebra

/-!
# Principal roots over arbitrary rings

The integral cyclotomic quotient is a domain. Its orthogonality identities
descend to `R[X]/Φₙ(X)` for every commutative ring `R`. The target quotient
need not be a domain, and the transform length need not be invertible in it.
No arithmetic cost for representing quotient elements is asserted here.
-/

namespace DivisionFree.Fourier

open Polynomial

variable (R : Type*) [CommRing R] (n : ℕ) [NeZero n]

abbrev CyclotomicRing := AdjoinRoot (cyclotomic n R)

noncomputable def cyclotomicRoot : CyclotomicRing R n :=
  AdjoinRoot.root (cyclotomic n R)

instance integerCyclotomicDomain : IsDomain (CyclotomicRing ℤ n) :=
  AdjoinRoot.isDomain_of_prime (cyclotomic.irreducible (NeZero.pos n)).prime

instance integerCyclotomicCharZero : CharZero (CyclotomicRing ℤ n) :=
  charZero_of_injective_ringHom
    (AdjoinRoot.of.injective_of_degree_ne_zero
      (ne_of_gt (degree_cyclotomic_pos n ℤ (NeZero.pos n))))

theorem integerRoot_primitive : IsPrimitiveRoot (cyclotomicRoot ℤ n) n := by
  apply (isRoot_cyclotomic_iff_charZero (NeZero.pos n)).mp
  rw [← map_cyclotomic_int n (CyclotomicRing ℤ n)]
  exact AdjoinRoot.isRoot_root (cyclotomic n ℤ)

/-- Base change is available even when the target coefficient ring is trivial. -/
noncomputable def cyclotomicBaseChange : CyclotomicRing ℤ n →+* CyclotomicRing R n :=
  AdjoinRoot.map (Int.castRingHom R) (cyclotomic n ℤ) (cyclotomic n R)
    (by rw [map_cyclotomic_int])

omit [NeZero n] in
@[simp] theorem cyclotomicBaseChange_root :
    cyclotomicBaseChange R n (cyclotomicRoot ℤ n) = cyclotomicRoot R n := by
  simp [cyclotomicBaseChange, cyclotomicRoot]

theorem cyclotomicRoot_pow : cyclotomicRoot R n ^ n = 1 := by
  have h := congrArg (cyclotomicBaseChange R n) (integerRoot_primitive n).pow_eq_one
  simpa using h

noncomputable def cyclotomicCharacter : AddChar (ZMod n) (CyclotomicRing R n) :=
  AddChar.zmodChar n (cyclotomicRoot_pow R n)

theorem cyclotomicCharacter_orthogonal : Orthogonal (cyclotomicCharacter R n) := by
  have h := (orthogonal_of_primitive (integerRoot_primitive n)).map
    (cyclotomicBaseChange R n)
  have heq : (cyclotomicBaseChange R n).toMonoidHom.compAddChar
      (AddChar.zmodChar n (integerRoot_primitive n).pow_eq_one) =
      cyclotomicCharacter R n := by
    ext t
    simp [cyclotomicCharacter, AddChar.zmodChar_apply]
  rw [heq] at h
  exact h

theorem cyclotomicSubroot_pow (d : ℕ) (hd : d ∣ n) :
    (cyclotomicRoot R n ^ (n / d)) ^ d = 1 := by
  rw [← pow_mul, Nat.div_mul_cancel hd, cyclotomicRoot_pow]

/-- A transform of any positive divisor length can be performed inside the
same cyclotomic extension. -/
noncomputable def cyclotomicSubcharacter (d : ℕ) [NeZero d] (hd : d ∣ n) :
    AddChar (ZMod d) (CyclotomicRing R n) :=
  AddChar.zmodChar d (cyclotomicSubroot_pow R n d hd)

theorem cyclotomicSubcharacter_orthogonal (d : ℕ) [NeZero d] (hd : d ∣ n) :
    Orthogonal (cyclotomicSubcharacter R n d hd) := by
  have hw : IsPrimitiveRoot (cyclotomicRoot ℤ n ^ (n / d)) d :=
    IsPrimitiveRoot.pow (NeZero.pos n) (integerRoot_primitive n) (Nat.div_mul_cancel hd).symm
  have h := (orthogonal_of_primitive hw).map (cyclotomicBaseChange R n)
  have heq : (cyclotomicBaseChange R n).toMonoidHom.compAddChar
      (AddChar.zmodChar d hw.pow_eq_one) = cyclotomicSubcharacter R n d hd := by
    ext t
    simp [cyclotomicSubcharacter, AddChar.zmodChar_apply]
  rw [heq] at h
  exact h

/-- A division-free Fourier product identity with no hypothesis on the base ring. -/
theorem cyclotomic_scaled_convolution (a b : ZMod n → CyclotomicRing R n) (k : ZMod n) :
    inverseTransform (cyclotomicCharacter R n)
      (fun j => transform (cyclotomicCharacter R n) a j *
        transform (cyclotomicCharacter R n) b j) k =
      (n : CyclotomicRing R n) * convolution a b k :=
  scaled_convolution _ (cyclotomicCharacter_orthogonal R n) a b k

end DivisionFree.Fourier
