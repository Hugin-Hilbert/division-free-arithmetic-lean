import DivisionFree.Fourier.FiniteTransform
import DivisionFree.Circuit
import DivisionFree.Constants

/-!
# Coefficient splitting for a mixed radix

The definitions in this file only rearrange coefficients and indices.  In
particular, the input split is a zero-cost wiring operation.
-/

namespace DivisionFree.Fourier

open DivisionFree
open scoped BigOperators

/-- The `k`th coefficient in the `m`-element block decomposition. -/
def splitCoefficients {R : Type*} (m n : ℕ) [NeZero m] [NeZero n]
    (x : ZMod (m * n) → R) (k : Fin n) (j : ZMod m) : R :=
  x ((n * j.val + k.val : ℕ) : ZMod (m * n))

/-- Split each of the two input channels into `n` blocks of length `m`.
Out-of-range block indices are padded by zero. -/
def splitInput (m n L : ℕ) [NeZero m] [NeZero n] :
    Circuit (Bool × ZMod (m * n)) (Bool × (Fin L × ZMod m)) :=
  .comp
    (.bundle (fun o : Bool × (Fin L × ZMod m) =>
      if o.2.1.val < n then
        .wire (fun _ : PUnit =>
          (o.1, ((n * o.2.2.val + o.2.1.val : ℕ) : ZMod (m * n))))
      else .zero))
    (.wire (fun o : Bool × (Fin L × ZMod m) => (o, PUnit.unit)))

@[simp] theorem splitInput_eval {R : Type*} [Ring R]
    (m n L : ℕ) [NeZero m] [NeZero n]
    (x : Bool × ZMod (m * n) → R) (b : Bool) (k : Fin L) (j : ZMod m) :
    (splitInput m n L).eval x (b, (k, j)) =
      if k.val < n then
        x (b, ((n * j.val + k.val : ℕ) : ZMod (m * n)))
      else 0 := by
  by_cases h : k.val < n <;> simp [splitInput, h]

theorem splitInput_cost (m n L : ℕ) [NeZero m] [NeZero n] :
    (splitInput m n L).cost = 0 := by
  classical
  simp only [splitInput, Circuit.comp_cost, Circuit.bundle_cost,
    Circuit.wire_cost]
  apply Finset.sum_eq_zero
  intro o ho
  split_ifs <;> simp

theorem splitInput_constantBits (m n L : ℕ) [NeZero m] [NeZero n] :
    (splitInput m n L).constantBits = 0 := by
  classical
  simp only [splitInput, Circuit.comp_constantBits, Circuit.constantBits]
  apply Finset.sum_eq_zero
  intro o ho
  split_ifs <;> simp [Circuit.constantBits]

/-- Regroup a length-`m*n` coefficient sum by the `n` blocks of length `m`.
No root-of-unity or invertibility hypothesis is needed for this indexing
identity. -/
theorem coefficientSum_split {R S : Type*} [CommRing R] [CommRing S]
    (m n : ℕ) [NeZero m] [NeZero n] (f : R →+* S)
    (x : ZMod (m * n) → R) (w : S) :
    (∑ i : ZMod (m * n), f (x i) * w ^ i.val) =
      ∑ k : Fin n,
        (∑ j : ZMod m,
          f (splitCoefficients m n x k j) * (w ^ n) ^ j.val) * w ^ k.val := by
  classical
  let e : Fin n × Fin m ≃ Fin (m * n) :=
    (Equiv.prodComm (Fin n) (Fin m)).trans finProdFinEquiv
  rw [← (cyclicIndexEquiv (m * n)).sum_comp
      (fun i : ZMod (m * n) =>
        f (x i) * w ^ i.val)]
  simp [cyclicIndexEquiv_apply, Nat.mod_eq_of_lt]
  rw [← e.sum_comp
      (fun p : Fin (m * n) =>
        f (x (p.val : ZMod (m * n))) * w ^ p.val)]
  simp only [e, Equiv.trans_apply, Equiv.prodComm_apply, finProdFinEquiv_apply_val,
    splitCoefficients]
  simp_rw [pow_add, pow_mul, Nat.mul_comm n]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro k
  simp only [Prod.swap]
  rw [Finset.sum_mul]
  apply Fintype.sum_equiv (cyclicIndexEquiv m)
  intro j
  simp [Nat.mod_eq_of_lt j.isLt, add_comm]
  ring

end DivisionFree.Fourier
