import DivisionFree.Polynomial.NewtonStep
import DivisionFree.Polynomial.NewtonCost

/-! The complete dyadic Newton inverse circuit, using the unconditional fast
multiplier. Each recursive result is computed once and then shared. -/

namespace DivisionFree.PolynomialArithmetic

universe u

noncomputable def inversePowerCircuit : (k : ℕ) → Circuit (Fin (2 ^ k)) (Fin (2 ^ k))
  | 0 => .integer 1
  | k + 1 =>
    .comp
      (.pair (.wire id)
        (.comp (resize (2 ^ (k + 1)) (2 ^ k))
          (.comp (inversePowerCircuit k) (resize (2 ^ k) (2 ^ (k + 1))))))
      (.comp (.wire fun j : Bool × Fin (2 ^ (k + 1)) =>
        if j.1 then Sum.inr j.2 else Sum.inl j.2)
        (newtonStepCircuit (fastMultiplier.{u} (2 ^ (k + 1)))))

theorem inversePowerCircuit_correct {R : Type u} [CommRing R]
    (k : ℕ) (x : Fin (2 ^ k) → R) (hx : (vectorPolynomial (2 ^ k) x).coeff 0 = 1) :
    (Polynomial.X : Polynomial R) ^ (2 ^ k) ∣
      1 - vectorPolynomial (2 ^ k) x *
        vectorPolynomial (2 ^ k) ((inversePowerCircuit.{u} k).eval x) := by
  induction k with
  | zero =>
    have hone : vectorPolynomial (2 ^ 0) ((inversePowerCircuit.{u} 0).eval x) = 1 := by
      simp [inversePowerCircuit, vectorPolynomial, Polynomial.ofFn_eq_sum_monomial]
    rw [hone, mul_one]
    simp only [pow_zero, pow_one]
    apply Polynomial.X_dvd_iff.mpr
    simp only [Polynomial.coeff_sub, Polynomial.coeff_one_zero]
    exact sub_eq_zero.mpr hx.symm
  | succ k ih =>
    let small := (resize (2 ^ (k + 1)) (2 ^ k)).eval x
    let v := (inversePowerCircuit.{u} k).eval small
    let y : Bool × Fin (2 ^ (k + 1)) → R := fun j =>
      if j.1 then (resize (2 ^ k) (2 ^ (k + 1))).eval v j.2 else x j.2
    have hsmall : (vectorPolynomial (2 ^ k) small).coeff 0 = 1 := by
      dsimp [small]
      rw [vectorPolynomial_resize_mod, modByMonic_X_pow_coeff,
        if_pos (by positivity), hx]
    have hrec := ih small hsmall
    change (Polynomial.X : Polynomial R) ^ (2 ^ k) ∣
      1 - vectorPolynomial (2 ^ k) small * vectorPolynomial (2 ^ k) v at hrec
    have hrec' : (Polynomial.X : Polynomial R) ^ (2 ^ k) ∣
        1 - vectorPolynomial (2 ^ (k + 1)) x * vectorPolynomial (2 ^ k) v := by
      dsimp [small] at hrec
      rw [vectorPolynomial_resize_mod, residual_mod_left_iff] at hrec
      exact hrec
    have hle : 2 ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hy : (Polynomial.X : Polynomial R) ^ (2 ^ k) ∣
        1 - vectorPolynomial (2 ^ (k + 1)) (fun i => y (false, i)) *
          vectorPolynomial (2 ^ (k + 1)) (fun i => y (true, i)) := by
      simp only [y, Bool.false_eq_true, if_false, if_true]
      rw [vectorPolynomial_resize_eq_of_le hle]
      exact hrec'
    have hstep := newtonStepCircuit_residual (fastMultiplier.{u} (2 ^ (k + 1))) y
      (2 ^ k) (by rw [pow_succ]; omega) hy
    have heval : (inversePowerCircuit.{u} (k + 1)).eval x =
        (newtonStepCircuit (fastMultiplier.{u} (2 ^ (k + 1)))).eval y := by
      funext i
      simp only [inversePowerCircuit, Circuit.eval_comp]
      apply congrArg (fun z : Bool × Fin (2 ^ (k + 1)) → R =>
        (newtonStepCircuit (fastMultiplier.{u} (2 ^ (k + 1)))).eval z i)
      funext j
      rcases j with ⟨b, j⟩
      cases b <;> simp [y, v, small]
    rw [heval]
    simpa only [y, Bool.false_eq_true, if_false] using hstep

@[simp] theorem inversePowerCircuit_base_cost : (inversePowerCircuit.{u} 0).cost = 0 := rfl

theorem inversePowerCircuit_step_cost (k : ℕ) :
    (inversePowerCircuit.{u} (k + 1)).cost = (inversePowerCircuit.{u} k).cost +
      2 * (fastMultiplier.{u} (2 ^ (k + 1))).cost + (twoMinus (2 ^ (k + 1))).cost := by
  simp only [inversePowerCircuit, Circuit.comp_cost, Circuit.pair_cost,
    Circuit.wire_cost, resize_cost, newtonStepCircuit_cost]
  omega

@[simp] theorem inversePowerCircuit_base_constantBits :
    (inversePowerCircuit.{u} 0).constantBits = 2 := by decide

theorem inversePowerCircuit_step_constantBits (k : ℕ) :
    (inversePowerCircuit.{u} (k + 1)).constantBits =
      (inversePowerCircuit.{u} k).constantBits +
      2 * (fastMultiplier.{u} (2 ^ (k + 1))).circuit.constantBits +
      (twoMinus (2 ^ (k + 1))).constantBits := by
  simp only [inversePowerCircuit, Circuit.comp_constantBits,
    Circuit.constantBits, resize_constantBits, newtonStepCircuit_constantBits]
  omega

theorem inversePowerCircuit_step_constantBits_le (k : ℕ) :
    (inversePowerCircuit.{u} (k + 1)).constantBits ≤ (inversePowerCircuit.{u} k).constantBits +
      60 * 2 ^ (k + 1) * (k + 3) + 3 := by
  rw [inversePowerCircuit_step_constantBits]
  have hm := fastMultiplier_constantBits_le (2 ^ (k + 1))
  have hlog : Nat.log 2 (2 * 2 ^ (k + 1)) = k + 2 := by
    rw [← pow_succ', Nat.log_pow (by decide)]
  rw [hlog] at hm
  have hsub := twoMinus_constantBits_le (2 ^ (k + 1))
  nlinarith

theorem inversePowerCircuit_constantBits_le (k : ℕ) :
    (inversePowerCircuit.{u} k).constantBits ≤ 120 * 2 ^ k * (k + 2) :=
  newtonBits_recurrence_bound (fun j => (inversePowerCircuit.{u} j).constantBits)
    (le_of_eq inversePowerCircuit_base_constantBits) inversePowerCircuit_step_constantBits_le k

end DivisionFree.PolynomialArithmetic
