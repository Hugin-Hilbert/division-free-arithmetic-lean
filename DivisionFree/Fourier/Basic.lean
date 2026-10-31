import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Tactic

/-!
# Fourier identities without division

Orthogonality is stated as an equality, so it survives every ring homomorphism,
including passage to positive characteristic and the zero ring. Inversion
returns the transform length times the input. It never divides by that length.
This file describes algebraic maps, not a fast transform implementation.
-/

namespace DivisionFree.Fourier

open scoped BigOperators

variable {n : ℕ} [NeZero n] {R S : Type*} [CommRing R] [CommRing S]

/-- The principal-root identity required for a division-free inverse transform. -/
def Orthogonal (χ : AddChar (ZMod n) R) : Prop :=
  ∀ t : ZMod n, ∑ j : ZMod n, χ (j * t) = if t = 0 then (n : R) else 0

/-- An unnormalized Fourier transform. -/
noncomputable def transform (χ : AddChar (ZMod n) R)
    (a : ZMod n → R) (k : ZMod n) : R :=
  ∑ j : ZMod n, a j * χ (j * k)

/-- The inverse-sign transform, still without division. -/
noncomputable def inverseTransform (χ : AddChar (ZMod n) R)
    (a : ZMod n → R) (k : ZMod n) : R :=
  ∑ j : ZMod n, a j * χ (-(j * k))

/-- Cyclic convolution of coefficient vectors. -/
noncomputable def convolution (a b : ZMod n → R) (k : ZMod n) : R :=
  ∑ j : ZMod n, a j * b (k - j)

theorem orthogonal_of_primitive [IsDomain R] {w : R}
    (hw : IsPrimitiveRoot w n) : Orthogonal (AddChar.zmodChar n hw.pow_eq_one) := by
  intro t
  simpa using AddChar.sum_mulShift t (AddChar.zmodChar_primitive_of_primitive_root n hw)

theorem Orthogonal.map {χ : AddChar (ZMod n) R} (hχ : Orthogonal χ)
    (f : R →+* S) : Orthogonal (f.toMonoidHom.compAddChar χ) := by
  intro t
  change (∑ j : ZMod n, f (χ (j * t))) = if t = 0 then (n : S) else 0
  rw [← map_sum, hχ t]
  by_cases ht : t = 0 <;> simp [ht]

theorem inverseTransform_transform (χ : AddChar (ZMod n) R)
    (hχ : Orthogonal χ) (a : ZMod n → R) (k : ZMod n) :
    inverseTransform χ (transform χ a) k = (n : R) * a k := by
  classical
  unfold inverseTransform transform
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm (j i : ZMod n) :
      a j * χ (j * i) * χ (-(i * k)) = a j * χ (i * (j - k)) := by
    rw [mul_assoc, ← χ.map_add_eq_mul]
    congr 2
    ring
  have hsum : ∀ t : ZMod n, ∑ j : ZMod n, χ (j * t) =
      if t = 0 then (n : R) else 0 := hχ
  simp_rw [hterm, ← Finset.mul_sum, hsum]
  simp [sub_eq_zero, mul_comm]

theorem transform_convolution (χ : AddChar (ZMod n) R)
    (a b : ZMod n → R) (k : ZMod n) :
    transform χ (convolution a b) k = transform χ a k * transform χ b k := by
  classical
  unfold transform convolution
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  calc
    ∑ i : ZMod n, a j * b (i - j) * χ (i * k) =
        ∑ l : ZMod n, a j * b l * χ ((j + l) * k) := by
      symm
      exact Fintype.sum_bijective _ (AddGroup.addLeft_bijective j) _ _
        (fun l => by simp)
    _ = ∑ l : ZMod n, a j * χ (j * k) * (b l * χ (l * k)) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [add_mul, χ.map_add_eq_mul]
      ring

/-- Pointwise products followed by the inverse-sign transform compute a scaled
cyclic convolution over every coefficient ring satisfying orthogonality. -/
theorem scaled_convolution (χ : AddChar (ZMod n) R) (hχ : Orthogonal χ)
    (a b : ZMod n → R) (k : ZMod n) :
    inverseTransform χ (fun j => transform χ a j * transform χ b j) k =
      (n : R) * convolution a b k := by
  have h : (fun j => transform χ a j * transform χ b j) =
      transform χ (convolution a b) :=
    funext fun j => (transform_convolution χ a b j).symm
  rw [h, inverseTransform_transform χ hχ]

end DivisionFree.Fourier
