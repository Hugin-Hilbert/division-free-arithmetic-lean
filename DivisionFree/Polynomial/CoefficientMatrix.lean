import DivisionFree.Polynomial.TruncatedPairing
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Basic

/-! The coefficient matrix of a matrix over truncated polynomials. The
reversed coefficient pairing makes its adjoint the polynomial transpose. -/

namespace DivisionFree.PolynomialArithmetic

open scoped BigOperators

variable {r s q : ℕ} {R : Type*} [CommRing R]

noncomputable def blockMul (A : Fin r → Fin s → Fin q → R)
    (x : Fin s → Fin q → R) : Fin r → Fin q → R :=
  fun i => ∑ j, mulVector (A i j) (x j)

def blockTranspose (A : Fin r → Fin s → Fin q → R) : Fin s → Fin r → Fin q → R :=
  fun j i => A i j

def blockReverse (x : Fin r → Fin q → R) : Fin r → Fin q → R :=
  fun i => reverse (x i)

theorem reverse_sum {ι : Type*} (t : Finset ι) (f : ι → Fin q → R) :
    reverse (∑ i ∈ t, f i) = ∑ i ∈ t, reverse (f i) := by
  funext j
  simp [reverse]

theorem blockMul_pairing (hq : 0 < q) (A : Fin r → Fin s → Fin q → R)
    (x : Fin s → Fin q → R) (y : Fin r → Fin q → R) :
    (∑ i, blockMul A x i ⬝ᵥ reverse (y i)) =
      ∑ j, x j ⬝ᵥ reverse (blockMul (blockTranspose A) y j) := by
  simp only [blockMul, blockTranspose, sum_dotProduct, reverse_sum, dotProduct_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact mulVector_pairing hq (A i j) (x j) (y i)

def flatten (x : Fin r → Fin q → R) : Fin (r * q) → R :=
  fun t => x (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2

def unflatten (x : Fin (r * q) → R) : Fin r → Fin q → R :=
  fun i j => x (finProdFinEquiv (i, j))

omit [CommRing R] in
@[simp] theorem unflatten_flatten (x : Fin r → Fin q → R) : unflatten (flatten x) = x := by
  funext i j
  simp [flatten, unflatten]

omit [CommRing R] in
@[simp] theorem flatten_unflatten (x : Fin (r * q) → R) : flatten (unflatten x) = x := by
  funext i
  change x (finProdFinEquiv (finProdFinEquiv.symm i)) = x i
  rw [Equiv.apply_symm_apply]

theorem flatten_dotProduct (x y : Fin r → Fin q → R) :
    flatten x ⬝ᵥ flatten y = ∑ i, x i ⬝ᵥ y i := by
  rw [dotProduct, ← finProdFinEquiv.sum_comp]
  simp [flatten, Fintype.sum_prod_type, dotProduct]

def reverseIndex (r q : ℕ) (t : Fin (r * q)) : Fin (r * q) :=
  finProdFinEquiv ((finProdFinEquiv.symm t).1, (finProdFinEquiv.symm t).2.rev)

@[simp] theorem reverseIndex_involutive (t : Fin (r * q)) :
    reverseIndex r q (reverseIndex r q t) = t := by
  simp only [reverseIndex, Equiv.symm_apply_apply, Fin.rev_rev]
  exact finProdFinEquiv.apply_symm_apply t

def reverseFlat (x : Fin (r * q) → R) : Fin (r * q) → R :=
  fun t => x (reverseIndex r q t)

omit [CommRing R] in
@[simp] theorem reverseFlat_involutive (x : Fin (r * q) → R) :
    reverseFlat (reverseFlat x) = x := by
  funext t
  simp [reverseFlat]

omit [CommRing R] in
theorem flatten_blockReverse (x : Fin r → Fin q → R) :
    flatten (blockReverse x) = reverseFlat (flatten x) := by
  funext t
  simp [flatten, blockReverse, reverse, reverseFlat, reverseIndex]

noncomputable def coefficientMap (A : Fin r → Fin s → Fin q → R)
    (x : Fin (s * q) → R) : Fin (r * q) → R :=
  flatten (blockMul A (unflatten x))

theorem coefficientMap_pairing (hq : 0 < q) (A : Fin r → Fin s → Fin q → R)
    (x : Fin (s * q) → R) (y : Fin (r * q) → R) :
    coefficientMap A x ⬝ᵥ reverseFlat y =
      x ⬝ᵥ reverseFlat (coefficientMap (blockTranspose A) y) := by
  have h := blockMul_pairing hq A (unflatten x) (unflatten y)
  rw [← flatten_dotProduct, ← flatten_dotProduct] at h
  change flatten (blockMul A (unflatten x)) ⬝ᵥ flatten (blockReverse (unflatten y)) =
    flatten (unflatten x) ⬝ᵥ
      flatten (blockReverse (blockMul (blockTranspose A) (unflatten y))) at h
  simpa only [flatten_blockReverse, flatten_unflatten, coefficientMap] using h

end DivisionFree.PolynomialArithmetic
