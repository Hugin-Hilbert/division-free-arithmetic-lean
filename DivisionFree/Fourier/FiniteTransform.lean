import DivisionFree.Fourier.Basic
import DivisionFree.Fourier.Radix
import DivisionFree.Fourier.Polynomial

/-!
# Bridge between cyclic and finite-index transforms
-/

namespace DivisionFree.Fourier

open scoped BigOperators

/-- Identify the canonical representatives of `ZMod n` with `Fin n`. -/
def cyclicIndexEquiv (n : ℕ) [NeZero n] : Fin n ≃ ZMod n where
  toFun i := (i.val : ZMod n)
  invFun j := ⟨j.val, ZMod.val_lt j⟩
  left_inv i := Fin.ext (by simp [ZMod.val_natCast_of_lt i.isLt])
  right_inv j := by
    apply ZMod.val_injective n
    simp

@[simp] theorem cyclicIndexEquiv_apply (n : ℕ) [NeZero n] (i : Fin n) :
    cyclicIndexEquiv n i = (i.val : ZMod n) := rfl

@[simp] theorem cyclicIndexEquiv_symm_apply (n : ℕ) [NeZero n] (j : ZMod n) :
    (cyclicIndexEquiv n).symm j = ⟨j.val, ZMod.val_lt j⟩ := rfl

theorem transform_fin {n : ℕ} [NeZero n] {R : Type*} [CommRing R]
    (χ : AddChar (ZMod n) R) (a : Fin n → R) (k : Fin n) :
    transform χ (fun j => a ((cyclicIndexEquiv n).symm j))
      (cyclicIndexEquiv n k) = finTransform (χ 1) a k := by
  classical
  unfold transform finTransform
  rw [← (cyclicIndexEquiv n).sum_comp
    (fun j : ZMod n => a ((cyclicIndexEquiv n).symm j) * χ (j * (cyclicIndexEquiv n k)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Equiv.symm_apply_apply]
  congr 1
  have h := χ.map_nsmul_eq_pow (i.val * k.val) (1 : ZMod n)
  simpa [nsmul_eq_mul, ← Nat.cast_mul] using h

theorem inverseTransform_eq_transform_neg {n : ℕ} [NeZero n]
    {R : Type*} [CommRing R] (χ : AddChar (ZMod n) R)
    (a : ZMod n → R) (k : ZMod n) :
    inverseTransform χ a k = transform χ a (-k) := by
  simp [inverseTransform, transform, mul_neg]

/-- The finite index representing the negative of a cyclic frequency. -/
def negIndex (n : ℕ) [NeZero n] (k : Fin n) : Fin n :=
  (cyclicIndexEquiv n).symm (-(cyclicIndexEquiv n k))

theorem finTransform_scaled_convolution {n : ℕ} [NeZero n]
    {R : Type*} [CommRing R] (χ : AddChar (ZMod n) R)
    (hχ : Orthogonal χ) (d : R) (a b : Fin n → R) (k : Fin n) :
    finTransform (χ 1)
        (fun i => d * (finTransform (χ 1) a i * finTransform (χ 1) b i))
        (negIndex n k) =
      d * (n : R) * convolution
        (fun j => a ((cyclicIndexEquiv n).symm j))
        (fun j => b ((cyclicIndexEquiv n).symm j))
        (cyclicIndexEquiv n k) := by
  let A : ZMod n → R := fun j => a ((cyclicIndexEquiv n).symm j)
  let B : ZMod n → R := fun j => b ((cyclicIndexEquiv n).symm j)
  rw [← transform_fin χ
    (fun i => d * (finTransform (χ 1) a i * finTransform (χ 1) b i))
    (negIndex n k)]
  simp only [negIndex, Equiv.apply_symm_apply]

  simp_rw [← transform_fin χ a, ← transform_fin χ b]
  simp_rw [Equiv.apply_symm_apply]
  rw [← inverseTransform_eq_transform_neg]
  change inverseTransform χ
      (fun j => d * (transform χ A j * transform χ B j))
      (cyclicIndexEquiv n k) = _
  calc
    inverseTransform χ (fun j => d * (transform χ A j * transform χ B j))
        (cyclicIndexEquiv n k) =
      d * inverseTransform χ (fun j => transform χ A j * transform χ B j)
        (cyclicIndexEquiv n k) := by
          unfold inverseTransform
          calc
            (∑ j : ZMod n, d * (transform χ A j * transform χ B j) * χ (-(j * cyclicIndexEquiv n k))) =
              ∑ j : ZMod n, d * ((transform χ A j * transform χ B j) * χ (-(j * cyclicIndexEquiv n k))) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
            _ = d * ∑ j : ZMod n,
                (transform χ A j * transform χ B j) * χ (-(j * cyclicIndexEquiv n k)) := by
                  rw [Finset.mul_sum]
    _ = d * ((n : R) * convolution A B (cyclicIndexEquiv n k)) := by
      rw [scaled_convolution χ hχ A B]
    _ = d * (n : R) * convolution A B (cyclicIndexEquiv n k) := by ring

end DivisionFree.Fourier
