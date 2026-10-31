import DivisionFree.Fourier.CyclicCircuits
import DivisionFree.Fourier.Cyclotomic
import DivisionFree.Fourier.Polynomial

/-! Cyclic coefficient arrays represent extension-ring values. Root multiplication
is a permutation of the coefficients, with no base-ring arithmetic gates. -/

namespace DivisionFree.Fourier

open scoped BigOperators

variable {m : ℕ} [NeZero m] {R S : Type*} [CommRing R] [CommRing S]

/-- Evaluate a redundant cyclic coefficient representation using a character. -/
noncomputable def cyclicEval (f : R →+* S) (χ : AddChar (ZMod m) S)
    (x : ZMod m → R) : S := ∑ j : ZMod m, f (x j) * χ j

@[simp] theorem cyclicEval_zero (f : R →+* S) (χ : AddChar (ZMod m) S) :
    cyclicEval f χ (fun _ => 0) = 0 := by simp [cyclicEval]

@[simp] theorem cyclicEval_add (f : R →+* S) (χ : AddChar (ZMod m) S)
    (x y : ZMod m → R) :
    cyclicEval f χ (fun j => x j + y j) = cyclicEval f χ x + cyclicEval f χ y := by
  simp [cyclicEval, add_mul, Finset.sum_add_distrib]

@[simp] theorem cyclicEval_neg (f : R →+* S) (χ : AddChar (ZMod m) S)
    (x : ZMod m → R) :
    cyclicEval f χ (fun j => -x j) = -cyclicEval f χ x := by
  simp [cyclicEval, Finset.sum_neg_distrib]

theorem cyclicEval_sum {I : Type*} [Fintype I] (f : R →+* S)
    (χ : AddChar (ZMod m) S) (x : I → ZMod m → R) :
    cyclicEval f χ (fun j => ∑ i : I, x i j) = ∑ i : I, cyclicEval f χ (x i) := by
  simp only [cyclicEval, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem cyclicEval_shift (f : R →+* S) (χ : AddChar (ZMod m) S)
    (e : ZMod m) (x : ZMod m → R) :
    cyclicEval f χ (fun j => x (j - e)) = χ e * cyclicEval f χ x := by
  unfold cyclicEval
  calc
    ∑ j : ZMod m, f (x (j - e)) * χ j =
        ∑ j : ZMod m, f (x j) * χ (e + j) := by
      symm
      exact Fintype.sum_bijective _ (AddGroup.addLeft_bijective e) _ _ (by intro j; simp)
    _ = χ e * ∑ j : ZMod m, f (x j) * χ j := by
      simp only [χ.map_add_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem cyclicShift_correct (f : R →+* S) (χ : AddChar (ZMod m) S)
    (e : ZMod m) (x : ZMod m → R) :
    cyclicEval f χ ((cyclicShift m e).eval x) = χ e * cyclicEval f χ x :=
  cyclicEval_shift f χ e x

theorem cyclicEval_eq_polynomial (f : R →+* S) (χ : AddChar (ZMod m) S)
    (x : ZMod m → R) :
    cyclicEval f χ x = (toPolynomial (fun j => f (x j))).eval (χ 1) := by
  simpa [cyclicEval, transform] using transform_eq_eval χ (fun j => f (x j)) 1

theorem cyclicEval_convolution (f : R →+* S) (χ : AddChar (ZMod m) S)
    (x y : ZMod m → R) :
    cyclicEval f χ (convolution x y) = cyclicEval f χ x * cyclicEval f χ y := by
  have h := transform_convolution χ (fun j => f (x j)) (fun j => f (y j)) 1
  simpa [cyclicEval, transform, convolution] using h

/-- The redundant representation maps to the actual cyclotomic quotient. -/
noncomputable def toCyclotomic (x : ZMod m → R) : CyclotomicRing R m :=
  cyclicEval (AdjoinRoot.of _) (cyclotomicCharacter R m) x

theorem toCyclotomic_eq_mk (x : ZMod m → R) :
    toCyclotomic x = AdjoinRoot.mk (Polynomial.cyclotomic m R) (toPolynomial x) := by
  simp only [toCyclotomic, cyclicEval, cyclotomicCharacter, AddChar.zmodChar_apply,
    toPolynomial, map_sum, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
    AdjoinRoot.mk_C, AdjoinRoot.mk_X, cyclotomicRoot]

theorem toCyclotomic_shift (e : ZMod m) (x : ZMod m → R) :
    toCyclotomic ((cyclicShift m e).eval x) =
      cyclotomicRoot R m ^ e.val * toCyclotomic x :=
  cyclicShift_correct (AdjoinRoot.of _) (cyclotomicCharacter R m) e x

end DivisionFree.Fourier
