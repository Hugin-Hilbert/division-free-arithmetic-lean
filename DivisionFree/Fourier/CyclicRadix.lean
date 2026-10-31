import DivisionFree.Fourier.CyclicRepresentation
import DivisionFree.Fourier.Radix

/-!
# FFT on cyclic coefficient representations

All twiddle multiplications are coefficient permutations. The exact cost below
counts base-ring additions, rather than treating extension-ring arithmetic as
a unit-cost operation. Canonical reduction and pointwise products are separate.
-/

namespace DivisionFree.Fourier

open scoped BigOperators
noncomputable section

variable (M : ℕ) [NeZero M]

private def arraySum {I : Type} (a b : Circuit I (ZMod M)) : Circuit I (ZMod M) :=
  .comp (.pair a b)
    (.comp (.wire fun j : Bool × ZMod M => if j.1 then .inr j.2 else .inl j.2)
      (cyclicAdd M))

private theorem arraySum_eval {I : Type} {R : Type*} [Ring R]
    (a b : Circuit I (ZMod M)) (x : I → R) (j : ZMod M) :
    (arraySum M a b).eval x j = a.eval x j + b.eval x j := by
  simp [arraySum]

private theorem arraySum_cost {I : Type} (a b : Circuit I (ZMod M)) :
    (arraySum M a b).cost = a.cost + b.cost + M := by simp [arraySum, cyclicAdd_cost]

private def arraySumList {I : Type} : List (Circuit I (ZMod M)) → Circuit I (ZMod M)
  | [] => .zero
  | a :: as => arraySum M a (arraySumList as)

private theorem arraySumList_eval {I : Type} {R : Type*} [Ring R]
    (ps : List (Circuit I (ZMod M))) (x : I → R) (j : ZMod M) :
    (arraySumList M ps).eval x j = (ps.map fun p => p.eval x j).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [arraySumList, arraySum_eval, ih]

private theorem arraySumList_cost {I : Type} (ps : List (Circuit I (ZMod M))) :
    (arraySumList M ps).cost = (ps.map Circuit.cost).sum + M * ps.length := by
  induction ps with
  | nil => simp [arraySumList]
  | cons p ps ih => simp [arraySumList, arraySum_cost, ih]; ring

private def cyclicStage (s n : ℕ) (hn : 0 < n) (e : ZMod M) :
    Circuit (Fin s × (Fin n × ZMod M)) (Fin (n * s) × ZMod M) :=
  .bundle fun k : Fin (n * s) => arraySumList M
    (Finset.univ.toList.map fun i : Fin s =>
      .wire fun j : ZMod M => (i, (⟨k.val % n, Nat.mod_lt _ hn⟩,
        j - (i.val * k.val) • e)))

private theorem cyclicStage_eval {R : Type*} [Ring R]
    (s n : ℕ) (hn : 0 < n) (e : ZMod M)
    (x : Fin s × (Fin n × ZMod M) → R) (k : Fin (n * s)) (j : ZMod M) :
    (cyclicStage M s n hn e).eval x (k, j) =
      ∑ i : Fin s, x (i, (⟨k.val % n, Nat.mod_lt _ hn⟩, j - (i.val * k.val) • e)) := by
  simp [cyclicStage, arraySumList_eval, List.map_map]

private theorem cyclicStage_cost (s n : ℕ) (hn : 0 < n) (e : ZMod M) :
    (cyclicStage M s n hn e).cost = M * s * (n * s) := by
  simp [cyclicStage, arraySumList_cost, List.map_map]
  ring

private theorem cyclicStage_correct {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (χ : AddChar (ZMod M) S)
    (s n : ℕ) (hn : 0 < n) (e : ZMod M)
    (x : Fin s × (Fin n × ZMod M) → R) (k : Fin (n * s)) :
    cyclicEval f χ (fun j => (cyclicStage M s n hn e).eval x (k, j)) =
      ∑ i : Fin s, χ e ^ (i.val * k.val) *
        cyclicEval f χ (fun j => x (i, (⟨k.val % n, Nat.mod_lt _ hn⟩, j))) := by
  simp only [cyclicStage_eval]
  rw [cyclicEval_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [cyclicEval_shift f χ ((i.val * k.val) • e)
    (fun j => x (i, (⟨k.val % n, Nat.mod_lt _ hn⟩, j))), χ.map_nsmul_eq_pow]

private def cyclicLayer (s n : ℕ) (hn : 0 < n) (e : ZMod M)
    (P : Circuit (Fin n × ZMod M) (Fin n × ZMod M)) :
    Circuit (Fin (n * s) × ZMod M) (Fin (n * s) × ZMod M) :=
  .comp (.bundle fun i : Fin s =>
    .comp (.wire fun j : Fin n × ZMod M => (finProdFinEquiv (j.1, i), j.2)) P)
    (cyclicStage M s n hn e)

private theorem cyclicLayer_cost (s n : ℕ) (hn : 0 < n) (e : ZMod M)
    (P : Circuit (Fin n × ZMod M) (Fin n × ZMod M)) :
    (cyclicLayer M s n hn e P).cost = s * P.cost + M * s * (n * s) := by
  simp [cyclicLayer, cyclicStage_cost]

/-- A radix transform on extension coefficients, built only from base-ring
additions and wires. The shift `e` specifies the transform root. -/
def cyclicRadix (s : ℕ) (hs : 0 < s) : (r : ℕ) → (e : ZMod M) →
    Circuit (Fin (s ^ r) × ZMod M) (Fin (s ^ r) × ZMod M)
  | 0, _ => .wire id
  | r + 1, e => cyclicLayer M s (s ^ r) (pow_pos hs r) e
      (cyclicRadix s hs r (s • e))

/-- Coefficient-level recursion, independent of the list order used to express
the finite sums. This exposes the recurrence for constructive finite layouts. -/
theorem cyclicRadix_succ_eval {R : Type*} [CommRing R]
    (s : ℕ) (hs : 0 < s) (r : ℕ) (e : ZMod M)
    (x : Fin (s ^ (r + 1)) × ZMod M → R)
    (k : Fin (s ^ (r + 1))) (j : ZMod M) :
    (cyclicRadix M s hs (r + 1) e).eval x (k, j) =
      ∑ i : Fin s, (cyclicRadix M s hs r (s • e)).eval
        (fun z => x (finProdFinEquiv (z.1, i), z.2))
        (⟨k.val % s ^ r, Nat.mod_lt _ (pow_pos hs r)⟩,
          j - (i.val * k.val) • e) := by
  change (cyclicLayer M s (s ^ r) (pow_pos hs r) e
    (cyclicRadix M s hs r (s • e))).eval x (k, j) = _
  simp only [cyclicLayer, Circuit.eval_comp, cyclicStage_eval,
    Circuit.eval_bundle]
  rfl

theorem cyclicRadix_cost (s : ℕ) (hs : 0 < s) (r : ℕ) (e : ZMod M) :
    (cyclicRadix M s hs r e).cost = M * s * r * s ^ r := by
  induction r generalizing e with
  | zero => simp [cyclicRadix]
  | succ r ih =>
    change (cyclicLayer M s (s ^ r) (pow_pos hs r) e
      (cyclicRadix M s hs r (s • e))).cost = _
    rw [cyclicLayer_cost, ih, pow_succ]
    ring

theorem cyclicRadix_correct {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (χ : AddChar (ZMod M) S) (s : ℕ) (hs : 0 < s) (r : ℕ)
    (e : ZMod M) (he : χ e ^ (s ^ r) = 1)
    (x : Fin (s ^ r) × ZMod M → R) (k : Fin (s ^ r)) :
    cyclicEval f χ (fun j => (cyclicRadix M s hs r e).eval x (k, j)) =
      finTransform (χ e) (fun i => cyclicEval f χ (fun j => x (i, j))) k := by
  induction r generalizing e with
  | zero => simp [cyclicRadix, finTransform, Fin.eq_zero k]
  | succ r ih =>
    change Fin (s ^ r * s) × ZMod M → R at x
    change Fin (s ^ r * s) at k
    change χ e ^ (s ^ r * s) = 1 at he
    change cyclicEval f χ (fun j =>
      (cyclicLayer M s (s ^ r) (pow_pos hs r) e
        (cyclicRadix M s hs r (s • e))).eval x (k, j)) =
      finTransform (χ e) (fun i => cyclicEval f χ (fun j => x (i, j))) k
    have hroot : χ (s • e) ^ (s ^ r) = 1 := by
      rw [χ.map_nsmul_eq_pow, ← pow_mul, Nat.mul_comm s (s ^ r), he]
    have hmiddle : (Circuit.bundle fun i : Fin s =>
        Circuit.comp (Circuit.wire fun j : Fin (s ^ r) × ZMod M =>
          (finProdFinEquiv (j.1, i), j.2)) (cyclicRadix M s hs r (s • e))).eval x =
        (fun z : Fin s × (Fin (s ^ r) × ZMod M) =>
          (cyclicRadix M s hs r (s • e)).eval
            (fun j => x (finProdFinEquiv (j.1, z.1), j.2)) z.2) := by
      funext z
      simp only [Circuit.eval_bundle, Circuit.eval_comp]
      rfl
    simp only [cyclicLayer, Circuit.eval_comp]
    rw [hmiddle, cyclicStage_correct, finTransform_radix s (s ^ r) (pow_pos hs r) (χ e) he]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only
    rw [ih (s • e) hroot, χ.map_nsmul_eq_pow]

/-- The transform root is a power of the canonical root of the cyclotomic
quotient. All operations of this circuit are over the base ring `R`. -/
theorem cyclicRadix_cyclotomic {R : Type*} [CommRing R]
    (s : ℕ) (hs : 0 < s) (r : ℕ) (hdiv : s ^ r ∣ M)
    (x : Fin (s ^ r) × ZMod M → R) (k : Fin (s ^ r)) :
    toCyclotomic (fun j =>
        (cyclicRadix M s hs r (M / s ^ r : ZMod M)).eval x (k, j)) =
      finTransform (cyclotomicRoot R M ^ (M / s ^ r))
        (fun i => toCyclotomic (fun j => x (i, j))) k := by
  let χ := cyclotomicCharacter R M
  have hperiod : (s ^ r) • (M / s ^ r : ZMod M) = 0 := by
    rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hdiv, ZMod.natCast_self]
  have he : χ (M / s ^ r : ZMod M) ^ (s ^ r) = 1 := by
    rw [← χ.map_nsmul_eq_pow, hperiod, χ.map_zero_eq_one]
  have hchar : χ (M / s ^ r : ZMod M) = cyclotomicRoot R M ^ (M / s ^ r) := by
    change cyclotomicRoot R M ^ (M / s ^ r : ZMod M).val = _
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (cyclotomicRoot_pow R M)]
  have h := cyclicRadix_correct M (AdjoinRoot.of _) χ s hs r _ he x k
  simpa only [toCyclotomic, hchar] using h

private theorem arraySum_multiplications {I : Type} (a b : Circuit I (ZMod M)) :
    (arraySum M a b).multiplications = a.multiplications + b.multiplications := by
  simp [arraySum, cyclicAdd, Circuit.multiplications]

private theorem arraySumList_multiplications {I : Type}
    (ps : List (Circuit I (ZMod M))) :
    (arraySumList M ps).multiplications = (ps.map Circuit.multiplications).sum := by
  induction ps with
  | nil => rfl
  | cons a as ih => simp [arraySumList, arraySum_multiplications, ih]

private theorem arraySum_constantBits {I : Type} (a b : Circuit I (ZMod M)) :
    (arraySum M a b).constantBits = a.constantBits + b.constantBits := by
  simp [arraySum, cyclicAdd, Circuit.constantBits]

private theorem arraySumList_constantBits {I : Type}
    (ps : List (Circuit I (ZMod M))) :
    (arraySumList M ps).constantBits = (ps.map Circuit.constantBits).sum := by
  induction ps with
  | nil => rfl
  | cons a as ih => simp [arraySumList, arraySum_constantBits, ih]

private theorem arraySum_negations {I : Type} (a b : Circuit I (ZMod M)) :
    (arraySum M a b).negations = a.negations + b.negations := by
  simp [arraySum, cyclicAdd, Circuit.negations]

private theorem arraySumList_negations {I : Type}
    (ps : List (Circuit I (ZMod M))) :
    (arraySumList M ps).negations = (ps.map Circuit.negations).sum := by
  induction ps with
  | nil => rfl
  | cons a as ih => simp [arraySumList, arraySum_negations, ih]

private theorem cyclicStage_multiplications (s n : ℕ) (hn : 0 < n) (e : ZMod M) :
    (cyclicStage M s n hn e).multiplications = 0 := by
  simp [cyclicStage, arraySumList_multiplications]

private theorem cyclicStage_constantBits (s n : ℕ) (hn : 0 < n) (e : ZMod M) :
    (cyclicStage M s n hn e).constantBits = 0 := by
  simp [cyclicStage, arraySumList_constantBits, Circuit.constantBits]

private theorem cyclicStage_negations (s n : ℕ) (hn : 0 < n) (e : ZMod M) :
    (cyclicStage M s n hn e).negations = 0 := by
  simp [cyclicStage, arraySumList_negations, Circuit.negations]

private theorem cyclicLayer_multiplications (s n : ℕ) (hn : 0 < n) (e : ZMod M)
    (P : Circuit (Fin n × ZMod M) (Fin n × ZMod M)) :
    (cyclicLayer M s n hn e P).multiplications = s * P.multiplications := by
  simp [cyclicLayer, cyclicStage_multiplications]

private theorem cyclicLayer_constantBits (s n : ℕ) (hn : 0 < n) (e : ZMod M)
    (P : Circuit (Fin n × ZMod M) (Fin n × ZMod M)) :
    (cyclicLayer M s n hn e P).constantBits = s * P.constantBits := by
  simp [cyclicLayer, cyclicStage_constantBits, Circuit.constantBits]

private theorem cyclicLayer_negations (s n : ℕ) (hn : 0 < n) (e : ZMod M)
    (P : Circuit (Fin n × ZMod M) (Fin n × ZMod M)) :
    (cyclicLayer M s n hn e P).negations = s * P.negations := by
  simp [cyclicLayer, cyclicStage_negations, Circuit.negations]

theorem cyclicRadix_multiplications (s : ℕ) (hs : 0 < s) (r : ℕ) (e : ZMod M) :
    (cyclicRadix M s hs r e).multiplications = 0 := by
  induction r generalizing e with
  | zero => simp [cyclicRadix]
  | succ r ih =>
    change (cyclicLayer M s (s ^ r) (pow_pos hs r) e
      (cyclicRadix M s hs r (s • e))).multiplications = 0
    rw [cyclicLayer_multiplications, ih]
    simp

theorem cyclicRadix_constantBits (s : ℕ) (hs : 0 < s) (r : ℕ) (e : ZMod M) :
    (cyclicRadix M s hs r e).constantBits = 0 := by
  induction r generalizing e with
  | zero => simp [cyclicRadix, Circuit.constantBits]
  | succ r ih =>
    change (cyclicLayer M s (s ^ r) (pow_pos hs r) e
      (cyclicRadix M s hs r (s • e))).constantBits = 0
    rw [cyclicLayer_constantBits, ih]
    simp

theorem cyclicRadix_negations (s : ℕ) (hs : 0 < s) (r : ℕ) (e : ZMod M) :
    (cyclicRadix M s hs r e).negations = 0 := by
  induction r generalizing e with
  | zero => simp [cyclicRadix, Circuit.negations]
  | succ r ih =>
    change (cyclicLayer M s (s ^ r) (pow_pos hs r) e
      (cyclicRadix M s hs r (s • e))).negations = 0
    rw [cyclicLayer_negations, ih]
    simp

end
end DivisionFree.Fourier
