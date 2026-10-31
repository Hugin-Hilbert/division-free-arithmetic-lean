import DivisionFree.Polynomial.PrimePowerFullMultiplication
import DivisionFree.Polynomial.ScaledMultiplication

/-! Exact multiplication-gate counts for the full-product wrappers. -/

namespace DivisionFree.Fourier

private theorem transported_multiplications {a b : ℕ} (h : a = b)
    (C : Circuit (ZMod a) (ZMod a)) : (h ▸ C).multiplications = C.multiplications := by
  cases h
  rfl

theorem primeNormalize_multiplications (p q : ℕ) (hp : p.Prime) :
    (primeNormalize p q hp).multiplications = 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hidx : (p - 1 + 1) * p ^ q = p ^ (q + 1) := by
    rw [Nat.sub_add_cancel hp.one_le, pow_succ]
    simp [Nat.mul_comm]
  change (hidx ▸ cyclicNormalize (p - 1) (p ^ q)).multiplications = 0
  rw [transported_multiplications]
  exact cyclicNormalize_multiplications _ _

theorem cyclicFullProduct_multiplications (n m : ℕ) [NeZero m]
    (P : Circuit (Bool × ZMod m) (ZMod m)) (N : Circuit (ZMod m) (ZMod m)) :
    (cyclicFullProduct n m P N).multiplications =
      P.multiplications + N.multiplications := by
  simp [cyclicFullProduct, cyclicInput_multiplications]

end DivisionFree.Fourier

namespace DivisionFree.PolynomialArithmetic

open Fourier

theorem primePowerFullMultiplier_multiplications (p n : ℕ) [NeZero p]
    (hp : p.Prime) (hn : 1 ≤ n) :
    (primePowerFullMultiplier p n hp hn).circuit.multiplications =
    (primePowerCircuit p (paddedExponent p n)).multiplications := by
  simp [primePowerFullMultiplier, cyclicFullProduct, paddedExponent,
    cyclicInput_multiplications, primeNormalize, cyclicNormalize_multiplications,
    transported_multiplications]

theorem combineScaledFullMultipliers_multiplications {n : ℕ} {d e u v : ℤ}
    (A : ScaledFullMultiplier n d) (B : ScaledFullMultiplier n e)
    (hbez : u * d + v * e = 1) :
    (combineScaledFullMultipliers A B hbez).circuit.multiplications =
      A.circuit.multiplications + B.circuit.multiplications + 4 * n := by
  classical
  let post : Circuit (Fin (2 * n) ⊕ Fin (2 * n)) (Fin (2 * n)) :=
    .comp (.bundle (fun k =>
      let left : Circuit (Fin (2 * n) ⊕ Fin (2 * n)) PUnit := .comp
        (.pair (.integer u) (.wire (fun _ : PUnit => Sum.inl k)))
        (.comp (.wire (fun b : Bool => if b then Sum.inr PUnit.unit else Sum.inl PUnit.unit)) .mul)
      let right : Circuit (Fin (2 * n) ⊕ Fin (2 * n)) PUnit := .comp
        (.pair (.integer v) (.wire (fun _ : PUnit => Sum.inr k)))
        (.comp (.wire (fun b : Bool => if b then Sum.inr PUnit.unit else Sum.inl PUnit.unit)) .mul)
      Circuit.sum left right)) (.wire fun k : Fin (2 * n) => (k, PUnit.unit))
  change A.circuit.multiplications + B.circuit.multiplications + post.multiplications = _
  dsimp [post]
  simp only [Circuit.comp_multiplications,
    Circuit.sum_multiplications, Circuit.pair_multiplications,
    Circuit.integer_multiplications, Circuit.wire_multiplications,
    Circuit.mul_multiplications, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  norm_num
  omega

end DivisionFree.PolynomialArithmetic
