import DivisionFree.Fourier.CyclicNormalization
import DivisionFree.Fourier.CyclicRepresentation
import DivisionFree.Fourier.BlockReduction

/-! Prime-power wrapper for cyclic coefficient normalization. -/

namespace DivisionFree.Fourier

open DivisionFree
open scoped BigOperators

private theorem primeNormalization_index (p q : ℕ) (hp : p.Prime) :
    ((p - 1) + 1) * p ^ q = p ^ (q + 1) := by
  rw [Nat.sub_add_cancel hp.one_le]
  rw [pow_succ]
  ring

private theorem transported_cost {n m : ℕ} (h : n = m)
    (C : Circuit (ZMod n) (ZMod n)) : (h ▸ C).cost = C.cost := by
  cases h
  rfl

private theorem transported_constantBits {n m : ℕ} (h : n = m)
    (C : Circuit (ZMod n) (ZMod n)) : (h ▸ C).constantBits = C.constantBits := by
  cases h
  rfl

private theorem transported_eval {n m : ℕ} {R : Type*} [Ring R]
    (h : n = m) (C : Circuit (ZMod n) (ZMod n))
    (x : ZMod m → R) (z : ZMod m) :
    (h ▸ C).eval x z = C.eval (h.symm ▸ x) (h.symm ▸ z) := by
  cases h
  rfl

private theorem transported_eval_fun {n m : ℕ} {R : Type*} [Ring R]
    (h : n = m) (C : Circuit (ZMod n) (ZMod n))
    (x : ZMod m → R) :
    (h ▸ C).eval x = h ▸ (C.eval (h.symm ▸ x)) := by
  cases h
  rfl

private theorem transported_cast_back {n m : ℕ} {R : Type*}
    (h : n = m) (x : ZMod m → R) : h ▸ (h.symm ▸ x) = x := by
  cases h
  rfl

private theorem transported_val {n m : ℕ} (h : n = m) (z : ZMod m) :
    (h.symm ▸ z).val = z.val := by
  cases h
  rfl

private theorem transported_toCyclotomic {n m : ℕ}
    [NeZero n] [NeZero m] {R : Type*} [CommRing R]
    (h : n = m) (x : ZMod n → R) :
    toCyclotomic (h ▸ x) = h ▸ toCyclotomic x := by
  cases h
  rfl

/-- Normalize a cyclic vector of length `p^(q+1)` into the prime-power
cyclotomic coefficient range. -/
noncomputable def primeNormalize (p q : ℕ) (hp : p.Prime) :
    Circuit (ZMod (p ^ (q + 1))) (ZMod (p ^ (q + 1))) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hidx := primeNormalization_index p q hp
  exact hidx ▸ cyclicNormalize (p - 1) (p ^ q)

theorem primeNormalize_cost (p q : ℕ) (hp : p.Prime) :
    (primeNormalize p q hp).cost = 2 * (p - 1) * p ^ q := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [primeNormalize]
  exact (transported_cost (primeNormalization_index p q hp)
    (cyclicNormalize (p - 1) (p ^ q))).trans (cyclicNormalize_cost _ _)

theorem primeNormalize_constantBits (p q : ℕ) (hp : p.Prime) :
    (primeNormalize p q hp).constantBits = 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [primeNormalize]
  exact (transported_constantBits (primeNormalization_index p q hp)
    (cyclicNormalize (p - 1) (p ^ q))).trans (cyclicNormalize_constantBits _ _)

theorem primeNormalize_correct {R : Type*} [CommRing R]
    (p q : ℕ) [NeZero (p ^ (q + 1))] (hp : p.Prime) (x : ZMod (p ^ (q + 1)) → R) :
    toCyclotomic ((primeNormalize p q hp).eval x) = toCyclotomic x := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ q) := ⟨Nat.ne_of_gt (pow_pos hp.pos q)⟩
  letI : NeZero ((p - 1 + 1) * p ^ q) := ⟨Nat.ne_of_gt (Nat.mul_pos (Nat.succ_pos _) (pow_pos hp.pos q))⟩
  have hidx := primeNormalization_index p q hp
  let x₀ : ZMod ((p - 1 + 1) * p ^ q) → R := hidx.symm ▸ x
  have hgeom := cyclotomicRoot_geom_sum (R := R) p q hp
  have hgeomSource : ∑ i : Fin p,
      cyclotomicRoot R ((p - 1 + 1) * p ^ q) ^ (p ^ q * i.val) = 0 := by
    have hgeomTarget := hgeom
    rw [← primeNormalization_index p q hp] at hgeomTarget
    exact hgeomTarget
  have hgeomBlock : ∑ i : Fin ((p - 1) + 1),
      cyclotomicRoot R ((p - 1 + 1) * p ^ q) ^ (p ^ q * i.val) = 0 := by
    let hFin : (p - 1) + 1 = p := Nat.sub_add_cancel hp.one_le
    let eFin : Fin p ≃ Fin ((p - 1) + 1) := (finCongr hFin).symm
    calc
      (∑ i : Fin ((p - 1) + 1),
          cyclotomicRoot R ((p - 1 + 1) * p ^ q) ^ (p ^ q * i.val)) =
        ∑ i : Fin p, cyclotomicRoot R ((p - 1 + 1) * p ^ q) ^
          (p ^ q * (eFin i).val) := (eFin.sum_comp _).symm
      _ = ∑ i : Fin p, cyclotomicRoot R ((p - 1 + 1) * p ^ q) ^ (p ^ q * i.val) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [eFin, finCongr_apply]
      _ = 0 := hgeomSource
  have hnorm := cyclicNormalize_correct (p - 1) (p ^ q)
    (AdjoinRoot.of _) (cyclotomicRoot R ((p - 1 + 1) * p ^ q)) hgeomBlock x₀
  have hnormC : toCyclotomic ((cyclicNormalize (p - 1) (p ^ q)).eval x₀) =
      toCyclotomic x₀ := by
    simpa [toCyclotomic, cyclicEval, cyclotomicCharacter,
      AddChar.zmodChar_apply] using hnorm
  have heval : (primeNormalize p q hp).eval x =
      hidx ▸ ((cyclicNormalize (p - 1) (p ^ q)).eval x₀) := by
    rw [primeNormalize]
    simpa [x₀] using transported_eval_fun hidx
      (cyclicNormalize (p - 1) (p ^ q)) x
  calc
    toCyclotomic ((primeNormalize p q hp).eval x) =
        toCyclotomic (hidx ▸ ((cyclicNormalize (p - 1) (p ^ q)).eval x₀)) := by
      rw [heval]
    _ = hidx ▸ toCyclotomic ((cyclicNormalize (p - 1) (p ^ q)).eval x₀) :=
      transported_toCyclotomic hidx _
    _ = hidx ▸ toCyclotomic x₀ := congrArg (fun z => hidx ▸ z) hnormC
    _ = toCyclotomic (hidx ▸ x₀) := (transported_toCyclotomic hidx x₀).symm
    _ = toCyclotomic x := by
      dsimp [x₀]
      rw [transported_cast_back hidx x]

theorem primeNormalize_tail {R : Type*} [CommRing R]
    (p q : ℕ) [NeZero (p ^ (q + 1))] (hp : p.Prime) (x : ZMod (p ^ (q + 1)) → R)
    (j : ZMod (p ^ (q + 1)))
    (hj : (p - 1) * p ^ q ≤ j.val) :
    (primeNormalize p q hp).eval x j = 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ q) := ⟨Nat.ne_of_gt (pow_pos hp.pos q)⟩
  letI : NeZero (p ^ (q + 1)) := ⟨Nat.ne_of_gt (pow_pos hp.pos (q + 1))⟩
  have hidx := primeNormalization_index p q hp
  let x₀ : ZMod ((p - 1 + 1) * p ^ q) → R := hidx.symm ▸ x
  let j₀ : ZMod ((p - 1 + 1) * p ^ q) := hidx.symm ▸ j
  have hjval : j₀.val = j.val := transported_val hidx j
  let e := cyclicBlocksEquiv (p - 1) (p ^ q)
  let ij := e.symm j₀
  have hval : j₀.val = ij.2.val + p ^ q * ij.1.val := by
    have heq : cyclicIndexEquiv ((p - 1 + 1) * p ^ q)
        (finProdFinEquiv (ij.1, ij.2)) = j₀ := by
      change e ij = j₀
      exact Equiv.apply_symm_apply e j₀
    have fi := finProdFinEquiv (ij.1, ij.2)
    have hvaleq := congrArg (fun z : ZMod ((p - 1 + 1) * p ^ q) => z.val) heq
    change ((finProdFinEquiv (ij.1, ij.2)).val :
      ZMod ((p - 1 + 1) * p ^ q)).val = j₀.val at hvaleq
    rw [ZMod.val_natCast_of_lt (finProdFinEquiv (ij.1, ij.2)).isLt] at hvaleq
    rw [finProdFinEquiv_apply_val] at hvaleq
    exact hvaleq.symm
  have hi : ij.1 = Fin.last (p - 1) := by
    apply Fin.ext
    by_contra hne
    have hival : ij.1.val < p := by
      simpa [Nat.sub_add_cancel hp.one_le] using ij.1.isLt
    have hlast : (Fin.last (p - 1)).val = p - 1 := rfl
    have hneval : ij.1.val ≠ p - 1 := by simpa [hlast] using hne
    have hi' : ij.1.val < p - 1 := by omega
    have hmul : (ij.1.val + 1) * p ^ q ≤ (p - 1) * p ^ q :=
      Nat.mul_le_mul_right (p ^ q) (Nat.succ_le_iff.mpr hi')
    have hstrict : ij.2.val + p ^ q * ij.1.val <
        (ij.1.val + 1) * p ^ q := by
      calc
        ij.2.val + p ^ q * ij.1.val < p ^ q + p ^ q * ij.1.val :=
          Nat.add_lt_add_right ij.2.isLt _
        _ = (ij.1.val + 1) * p ^ q := by ring
    have hj₀ : (p - 1) * p ^ q ≤ j₀.val := by rw [hjval]; exact hj
    have hbelow : j₀.val < (p - 1) * p ^ q := by
      rw [hval]
      exact Nat.lt_of_lt_of_le hstrict hmul
    omega
  have hpair : ij = (Fin.last (p - 1), ij.2) := Prod.ext hi rfl
  have hblock : j₀ = e (Fin.last (p - 1), ij.2) := by
    calc
      j₀ = e ij := (Equiv.apply_symm_apply e j₀).symm
      _ = e (Fin.last (p - 1), ij.2) := congrArg e hpair
  calc
    (primeNormalize p q hp).eval x j =
        (cyclicNormalize (p - 1) (p ^ q)).eval x₀ j₀ := by
      rw [primeNormalize]
      exact transported_eval hidx _ _ _
    _ = 0 := by
      rw [hblock]
      exact cyclicNormalize_eval_last (p - 1) (p ^ q) x₀ ij.2

end DivisionFree.Fourier
