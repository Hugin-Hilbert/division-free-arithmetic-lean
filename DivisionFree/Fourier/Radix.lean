import DivisionFree.Fourier.Basic
import DivisionFree.Polynomial.Encoding

/-!
# A radix transform circuit

The input contains an explicit table of powers of the root and the coefficient
vector. The circuit shares all recursive transforms and has `2*s*r*s^r` gates.
Preparing the root table and representing extension-ring operations over the
base ring are separate tasks; this module does not make either cost free in a
polynomial multiplication algorithm.
-/

namespace DivisionFree.Fourier

open scoped BigOperators
noncomputable section

private def lowerInputs (s m : ℕ) (i : Fin s) :
    Circuit (Fin (m * s) ⊕ Fin (m * s)) (Fin m ⊕ Fin m) :=
  .wire fun j => match j with
    | .inl j => .inl (finProdFinEquiv (j, ⟨0, lt_of_le_of_lt (Nat.zero_le i.val) i.isLt⟩))
    | .inr j => .inr (finProdFinEquiv (j, i))

private def radixTerm (s m : ℕ) (hs : 0 < s) (hm : 0 < m)
    (k : Fin (m * s)) (i : Fin s) :
    Circuit (Fin (m * s) ⊕ (Fin s × Fin m)) PUnit :=
  .comp (.wire fun b : Bool => if b then
      .inr (i, ⟨k.val % m, Nat.mod_lt _ hm⟩)
    else .inl ⟨(i.val * k.val) % (m * s), Nat.mod_lt _ (Nat.mul_pos hm hs)⟩)
    .mul

private def radixStage (s m : ℕ) (hs : 0 < s) (hm : 0 < m) :
    Circuit (Fin (m * s) ⊕ (Fin s × Fin m)) (Fin (m * s)) :=
  .comp (.bundle fun k => Circuit.sumList
    (Finset.univ.toList.map (radixTerm s m hs hm k)))
    (.wire fun k => (k, PUnit.unit))

private theorem radixStage_eval {R : Type*} [CommRing R]
    (s m : ℕ) (hs : 0 < s) (hm : 0 < m)
    (p : Fin (m * s) → R) (y : Fin s × Fin m → R) (k : Fin (m * s)) :
    (radixStage s m hs hm).eval (Sum.elim p y) k =
      ∑ i : Fin s, p ⟨(i.val * k.val) % (m * s), Nat.mod_lt _ (Nat.mul_pos hm hs)⟩ *
        y (i, ⟨k.val % m, Nat.mod_lt _ hm⟩) := by
  classical
  simp [radixStage, radixTerm, Circuit.sumList_eval, List.map_map]

private theorem radixStage_cost (s m : ℕ) (hs : 0 < s) (hm : 0 < m) :
    (radixStage s m hs hm).cost = 2 * s * (m * s) := by
  classical
  simp [radixStage, radixTerm, Circuit.sumList_cost, List.map_map]
  ring

private def radixLayer (s m : ℕ) (hs : 0 < s) (hm : 0 < m)
    (P : Circuit (Fin m ⊕ Fin m) (Fin m)) :
    Circuit (Fin (m * s) ⊕ Fin (m * s)) (Fin (m * s)) :=
  .comp (.pair (.wire Sum.inl)
    (.bundle fun i : Fin s => .comp (lowerInputs s m i) P))
    (radixStage s m hs hm)

private theorem radixLayer_cost (s m : ℕ) (hs : 0 < s) (hm : 0 < m)
    (P : Circuit (Fin m ⊕ Fin m) (Fin m)) :
    (radixLayer s m hs hm P).cost = s * P.cost + 2 * s * (m * s) := by
  simp [radixLayer, lowerInputs, radixStage_cost]

/-- Radix-`s` transform of length `s^r`, supplied with a table of root powers. -/
def radixTransform (s : ℕ) (hs : 0 < s) : (r : ℕ) →
    Circuit (Fin (s ^ r) ⊕ Fin (s ^ r)) (Fin (s ^ r))
  | 0 => .wire Sum.inr
  | r + 1 =>
    radixLayer s (s ^ r) hs (pow_pos hs r) (radixTransform s hs r)

theorem radixTransform_cost (s : ℕ) (hs : 0 < s) (r : ℕ) :
    (radixTransform s hs r).cost = 2 * s * r * s ^ r := by
  induction r with
  | zero => simp [radixTransform]
  | succ r ih =>
    change (radixLayer s (s ^ r) hs (pow_pos hs r) (radixTransform s hs r)).cost = _
    rw [radixLayer_cost, ih, pow_succ]
    ring

/-- The finite-vector specification for a transform. -/
def finTransform {R : Type*} [CommRing R] {n : ℕ}
    (w : R) (a : Fin n → R) (k : Fin n) : R :=
  ∑ j : Fin n, a j * w ^ (j.val * k.val)

theorem finTransform_eq_eval {R : Type*} [CommRing R] {n : ℕ}
    (w : R) (a : Fin n → R) (k : Fin n) :
    finTransform w a k =
      (PolynomialArithmetic.vectorPolynomial n a).eval (w ^ k.val) := by
  classical
  simp [finTransform, PolynomialArithmetic.vectorPolynomial,
    Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum, pow_mul, Nat.mul_comm]

theorem finTransform_radix {R : Type*} [CommRing R]
    (s m : ℕ) (hm : 0 < m) (w : R) (hw : w ^ (m * s) = 1)
    (a : Fin (m * s) → R) (k : Fin (m * s)) :
    finTransform w a k = ∑ i : Fin s, w ^ (i.val * k.val) *
      finTransform (w ^ s) (fun j => a (finProdFinEquiv (j, i)))
        ⟨k.val % m, Nat.mod_lt _ hm⟩ := by
  have hws : (w ^ s) ^ m = 1 := by
    rw [← pow_mul, Nat.mul_comm s m, hw]
  unfold finTransform
  rw [← finProdFinEquiv.sum_comp (fun j : Fin (m * s) => a j * w ^ (j.val * k.val)),
    Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hp : (w ^ s) ^ (j.val * (k.val % m)) = (w ^ s) ^ (j.val * k.val) := by
    rw [pow_eq_pow_mod (j.val * (k.val % m)) hws, pow_eq_pow_mod (j.val * k.val) hws]
    simp [Nat.mul_mod]
  simp only [finProdFinEquiv_apply_val]
  rw [hp, show (i.val + s * j.val) * k.val = i.val * k.val + s * (j.val * k.val) by ring,
    pow_add, pow_mul]
  ring

/-- Correctness of the actual recursive circuit. All root powers are supplied
as explicit parameters; no division or primitive-root assumption is needed. -/
theorem radixTransform_eval {R : Type*} [CommRing R]
    (s : ℕ) (hs : 0 < s) (r : ℕ) (w : R) (hw : w ^ (s ^ r) = 1)
    (a : Fin (s ^ r) → R) (k : Fin (s ^ r)) :
    (radixTransform s hs r).eval (Sum.elim (fun j => w ^ j.val) a) k =
      finTransform w a k := by
  induction r generalizing w with
  | zero =>
    simp [radixTransform, finTransform, Fin.eq_zero k]
  | succ r ih =>
    change Fin (s ^ r * s) → R at a
    change Fin (s ^ r * s) at k
    change w ^ (s ^ r * s) = 1 at hw
    change (radixLayer s (s ^ r) hs (pow_pos hs r) (radixTransform s hs r)).eval
      (Sum.elim (fun j => w ^ j.val) a) k = finTransform w a k
    have hm : 0 < s ^ r := pow_pos hs r
    have hws : (w ^ s) ^ (s ^ r) = 1 := by
      rw [← pow_mul, Nat.mul_comm s (s ^ r)]
      exact hw
    have hlow (i : Fin s) :
        (lowerInputs s (s ^ r) i).eval (Sum.elim (fun j => w ^ j.val) a) =
          Sum.elim (fun j => (w ^ s) ^ j.val)
            (fun j => a (finProdFinEquiv (j, i))) := by
      funext j
      cases j with
      | inl j => simp [lowerInputs, finProdFinEquiv_apply_val, pow_mul]
      | inr j => rfl
    have hbranch : (fun z : Fin s × Fin (s ^ r) =>
        (radixTransform s hs r).eval
          ((lowerInputs s (s ^ r) z.1).eval (Sum.elim (fun j => w ^ j.val) a)) z.2) =
        (fun z : Fin s × Fin (s ^ r) =>
          finTransform (w ^ s) (fun j => a (finProdFinEquiv (j, z.1))) z.2) := by
      funext z
      rw [hlow, ih _ hws]
    have hpair : (Circuit.pair (Circuit.wire Sum.inl)
        (Circuit.bundle (fun i : Fin s =>
          Circuit.comp (lowerInputs s (s ^ r) i) (radixTransform s hs r)))).eval
        (Sum.elim (fun j => w ^ j.val) a) =
        Sum.elim (fun j => w ^ j.val)
          (fun z => (radixTransform s hs r).eval
            ((lowerInputs s (s ^ r) z.1).eval (Sum.elim (fun j => w ^ j.val) a)) z.2) := by
      funext z
      cases z <;> simp
    change (radixLayer s (s ^ r) hs hm (radixTransform s hs r)).eval
      (Sum.elim (fun j => w ^ j.val) a) k = _
    rw [radixLayer, Circuit.eval_comp, hpair]
    rw [hbranch, radixStage_eval, finTransform_radix s (s ^ r) hm w hw]
    apply Finset.sum_congr rfl
    intro i _
    rw [← pow_eq_pow_mod (i.val * k.val) hw]

theorem radixTransform_eval_polynomial {R : Type*} [CommRing R]
    (s : ℕ) (hs : 0 < s) (r : ℕ) (w : R) (hw : w ^ (s ^ r) = 1)
    (a : Fin (s ^ r) → R) (k : Fin (s ^ r)) :
    (radixTransform s hs r).eval (Sum.elim (fun j => w ^ j.val) a) k =
      (PolynomialArithmetic.vectorPolynomial (s ^ r) a).eval (w ^ k.val) := by
  rw [radixTransform_eval s hs r w hw, finTransform_eq_eval]

end
end DivisionFree.Fourier
