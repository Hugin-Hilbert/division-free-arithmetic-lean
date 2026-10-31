import DivisionFree.Circuit.TruncatedLift
import DivisionFree.Polynomial.TruncatedQuotient

namespace DivisionFree

universe u
namespace PolynomialArithmetic

theorem toTruncated_neg {R : Type*} [CommRing R] {q : ℕ}
    (x : Fin q → R) :
    toTruncated (-x) = -toTruncated x := by
  have h : toTruncated (-x) + toTruncated x = 0 := by
    rw [← toTruncated_add, neg_add_cancel]
    exact toTruncated_zero
  exact (eq_neg_of_add_eq_zero_left h)

theorem toTruncated_constant {R : Type*} [CommRing R] {q : ℕ}
    (z : R) :
    toTruncated (fun i : Fin q => if i.val = 0 then z else 0) =
      (z : TruncatedRing R q) := by
  classical
  change AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ q)
      (vectorPolynomial q (fun i : Fin q => if i.val = 0 then z else 0)) =
    AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ q) (Polynomial.C z)
  rw [AdjoinRoot.mk_eq_mk]
  apply (Polynomial.X_pow_dvd_iff).2
  intro i hi
  rw [Polynomial.coeff_sub]
  have hv : (vectorPolynomial q (fun j : Fin q => if j.val = 0 then z else 0)).coeff i =
      (Polynomial.C z).coeff i := by
    by_cases h0 : i = 0
    · subst i
      rw [vectorPolynomial_coeff_of_lt q 0 _ hi]
      simp
    · by_cases hq : i < q
      · rw [vectorPolynomial_coeff_of_lt q i _ hq]
        rw [Polynomial.coeff_C_of_ne_zero h0]
        simp [h0]
      · rw [vectorPolynomial_coeff_eq_zero_of_ge q i _ (Nat.le_of_not_gt hq)]
        simp [Polynomial.coeff_C, h0]
  rw [hv]
  exact sub_self _

end PolynomialArithmetic

namespace Circuit

open PolynomialArithmetic

theorem truncatedLiftMul_eval {R : Type u} [CommRing R] (q : ℕ)
    (x : Bool × Fin q → R) :
    toTruncated (fun i : Fin q =>
      (truncatedLiftMul.{u} q).eval x (PUnit.unit, i)) =
      toTruncated (fun i => x (false, i)) * toTruncated (fun i => x (true, i)) := by
  have hv : (fun i : Fin q =>
      (truncatedLiftMul.{u} q).eval x (PUnit.unit, i)) =
      mulVector (fun i => x (false, i)) (fun i => x (true, i)) := by
    funext i
    simp [truncatedLiftMul, Circuit.eval_comp, fastMultiplier_correct, mulVector]
  rw [hv]
  exact toTruncated_mulVector _ _

set_option maxHeartbeats 1000000 in
theorem truncatedLiftAux_correct {R : Type u} [CommRing R]
    {I O : Type} (q : ℕ) (fO : Fintype O) (C : Circuit I O)
    (x : I × Fin q → R) (o : O) :
    toTruncated (fun i : Fin q => (truncatedLiftAux.{u} q fO C).eval x (o, i)) =
      C.eval (fun j => toTruncated (fun i : Fin q => x (j, i))) o := by
  classical
  induction C with
  | wire select =>
      simp [truncatedLiftAux, Circuit.eval]
  | zero =>
      simp [truncatedLiftAux, toTruncated_zero]
  | integer z =>
      have hv : (fun i : Fin q =>
          (truncatedLiftAux.{u} q fO (.integer z)).eval x (o, i)) =
          (fun i => if i.val = 0 then (z : R) else 0) := by
        funext i
        by_cases h : i.val = 0 <;>
          simp [truncatedLiftAux, Circuit.eval_comp, Circuit.eval_wire, h]
      rw [hv]
      simpa using toTruncated_constant (z : R)
  | add =>
      simp only [truncatedLiftAux, truncatedLiftAdd, Circuit.eval_comp,
        Circuit.eval_bundle, Circuit.eval_wire, Circuit.eval_add]
      change toTruncated ((fun i : Fin q => x (false, i)) +
        (fun i : Fin q => x (true, i))) = _
      exact toTruncated_add _ _
  | neg =>
      simp only [truncatedLiftAux, truncatedLiftNeg, Circuit.eval_comp,
        Circuit.eval_bundle, Circuit.eval_wire, Circuit.eval_neg]
      change toTruncated (-(fun i : Fin q => x (PUnit.unit, i))) = _
      exact toTruncated_neg _
  | mul =>
      cases o
      simp only [truncatedLiftAux, Circuit.eval_mul]
      exact truncatedLiftMul_eval (R := R) q x
  | @comp I J O inst first second ihFirst ihSecond =>
      letI := inst
      simp only [truncatedLiftAux, Circuit.eval_comp]
      calc
        toTruncated (fun i : Fin q =>
            (truncatedLiftAux.{u} q fO second).eval
              ((truncatedLiftAux.{u} q inst first).eval x) (o, i)) =
          second.eval (fun j => toTruncated (fun i : Fin q =>
            (truncatedLiftAux.{u} q inst first).eval x (j, i))) o := by
              exact ihSecond fO (fun p : J × Fin q =>
                (truncatedLiftAux.{u} q inst first).eval x p) o
        _ = second.eval
            (fun j => first.eval (fun a => toTruncated (fun i : Fin q => x (a, i))) j) o := by
              congr 1
              funext j
              exact ihFirst inst x j
  | @pair I O P left right ihLeft ihRight =>
      letI : Fintype (O ⊕ P) := fO
      letI : Fintype O := Fintype.ofInjective (fun a : O => (Sum.inl a : O ⊕ P))
        (by intro a b h; exact Sum.inl.inj h)
      letI : Fintype P := Fintype.ofInjective (fun b : P => (Sum.inr b : O ⊕ P))
        (by intro a b h; exact Sum.inr.inj h)
      cases o with
      | inl a =>
          simpa only [truncatedLiftAux, Circuit.eval_comp, Circuit.eval_pair_inl,
            Circuit.eval_wire] using ihLeft ‹Fintype O› x a
      | inr b =>
          simpa only [truncatedLiftAux, Circuit.eval_comp, Circuit.eval_pair_inr,
            Circuit.eval_wire] using ihRight ‹Fintype P› x b
  | @bundle I J O inst branches ih =>
      letI := inst
      cases o with
      | mk j a =>
          letI : Fintype (J × O) := fO
          have hJ : Nonempty J := ⟨j⟩
          letI : Fintype O := Fintype.ofInjective
            (fun z => (Classical.choice hJ, z))
            (by intro x y h; exact congrArg Prod.snd h)
          simpa only [truncatedLiftAux,
            dif_pos hJ, Circuit.eval_comp,
            Circuit.eval_bundle, Circuit.eval_wire] using ih j ‹Fintype O› x a

theorem truncatedLift_correct {R : Type u} [CommRing R]
    {I O : Type} [Fintype O] (q : ℕ) (C : Circuit I O)
    (x : I × Fin q → R) (o : O) :
    toTruncated (fun i : Fin q => (truncatedLift.{u} q C).eval x (o, i)) =
      C.eval (fun j => toTruncated (fun i : Fin q => x (j, i))) o := by
  exact truncatedLiftAux_correct q ‹Fintype O› C x o

end Circuit

end DivisionFree
