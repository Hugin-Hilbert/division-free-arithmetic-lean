import DivisionFree.Fourier.TwistedPolynomialProduct
import DivisionFree.Fourier.TernaryRecovery

/-! A full polynomial product from two length-`3^r` cyclic products. This is
the two-transform-length construction of Cantor--Kaltofen, Lemma 2.2. -/

namespace DivisionFree.Fourier

open scoped BigOperators
noncomputable section

variable (M : ℕ) [NeZero M]

def ternaryCyclicPair (r : ℕ) (e t : ZMod M)
    (P : Circuit (Bool × ZMod M) (ZMod M)) :
    Circuit (Bool × (Fin (3 ^ r) × ZMod M)) (Bool × (Fin (3 ^ r) × ZMod M)) :=
  .bundle fun b : Bool =>
    if b then twistedCyclicProduct M 3 (by decide) r e t P
    else cyclicProduct M 3 (by decide) r e P

def ternaryRecoverRows (n : ℕ) (e : ZMod M) :
    Circuit (Bool × (Fin n × ZMod M)) (Fin n × (Bool × ZMod M)) :=
  .bundle fun k : Fin n =>
    .comp (.wire fun bj : Bool × ZMod M => (bj.1, (k, bj.2)))
      (ternaryRecovery M e)

/-- Join the low and high coefficient arrays by a wire. -/
def twoBlockJoin (n : ℕ) :
    Circuit (Fin n × (Bool × ZMod M)) (Fin (2 * n) × ZMod M) :=
  .wire fun kj => if h : kj.1.val < n then (⟨kj.1.val, h⟩, (false, kj.2))
    else (⟨kj.1.val - n, by have := kj.1.isLt; omega⟩, (true, kj.2))

/-- Compute both cyclic products once, recover both halves, then join them. -/
def ternaryProduct (r : ℕ) (e t : ZMod M)
    (P : Circuit (Bool × ZMod M) (ZMod M)) :
    Circuit (Bool × (Fin (3 ^ r) × ZMod M)) (Fin (2 * 3 ^ r) × ZMod M) :=
  .comp (ternaryCyclicPair M r e t P)
    (.comp (ternaryRecoverRows M (3 ^ r) (3 ^ r • t)) (twoBlockJoin M (3 ^ r)))

theorem ternaryProduct_cost (r : ℕ) (e t : ZMod M)
    (P : Circuit (Bool × ZMod M) (ZMod M)) :
    (ternaryProduct M r e t P).cost =
      18 * M * r * 3 ^ r + 2 * 3 ^ r * P.cost + 8 * M * 3 ^ r := by
  simp [ternaryProduct, ternaryCyclicPair, ternaryRecoverRows, twoBlockJoin,
    twistedCyclicProduct_cost, cyclicProduct_cost, ternaryRecovery_cost]
  ring

theorem ternaryProduct_multiplications (r : ℕ) (e t : ZMod M)
    (P : Circuit (Bool × ZMod M) (ZMod M)) :
    (ternaryProduct M r e t P).multiplications = 2 * 3 ^ r * P.multiplications := by
  simp [ternaryProduct, ternaryCyclicPair, ternaryRecoverRows, twoBlockJoin,
    twistedCyclicProduct_multiplications, cyclicProduct_multiplications,
    ternaryRecovery_multiplications]
  ring

theorem ternaryProduct_constantBits (r : ℕ) (e t : ZMod M)
    (P : Circuit (Bool × ZMod M) (ZMod M)) :
    (ternaryProduct M r e t P).constantBits = 2 * 3 ^ r * P.constantBits := by
  simp [ternaryProduct, ternaryCyclicPair, ternaryRecoverRows, twoBlockJoin,
    twistedCyclicProduct_constantBits, cyclicProduct_constantBits,
    ternaryRecovery_constantBits, Circuit.constantBits]
  ring

theorem ternaryProduct_correct {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (χ : AddChar (ZMod M) S) (r : ℕ)
    (ψ : AddChar (ZMod (3 ^ r)) S) (hψ : Orthogonal ψ)
    (e t : ZMod M) (he : χ e = ψ 1)
    (hζ : 1 + χ (3 ^ r • t) + χ (3 ^ r • t) ^ 2 = 0) (d : S)
    (P : Circuit (Bool × ZMod M) (ZMod M))
    (hP : ∀ z : Bool × ZMod M → R,
      cyclicEval f χ (P.eval z) = d *
        (cyclicEval f χ (fun j => z (false, j)) *
          cyclicEval f χ (fun j => z (true, j))))
    (p q : Polynomial S)
    (hp : ∀ k, 3 ^ r ≤ k → p.coeff k = 0)
    (hq : ∀ k, 3 ^ r ≤ k → q.coeff k = 0)
    (hpq : ∀ k, 2 * 3 ^ r ≤ k → (p * q).coeff k = 0)
    (x : Bool × (Fin (3 ^ r) × ZMod M) → R)
    (hx₀ : ∀ i : Fin (3 ^ r),
      cyclicEval f χ (fun j => x (false, (i, j))) = p.coeff i.val)
    (hx₁ : ∀ i : Fin (3 ^ r),
      cyclicEval f χ (fun j => x (true, (i, j))) = q.coeff i.val)
    (k : Fin (2 * 3 ^ r)) :
    cyclicEval f χ (fun j => (ternaryProduct M r e t P).eval x (k, j)) =
      d * ((3 ^ (r + 1) : ℕ) : S) * (p * q).coeff k.val := by
  let y := (ternaryCyclicPair M r e t P).eval x
  have hD (i : Fin (3 ^ r)) : cyclicEval f χ (fun j => y (false, (i, j))) =
      d * ((3 ^ r : ℕ) : S) * ((p * q).coeff i.val + (p * q).coeff (3 ^ r + i.val)) := by
    change cyclicEval f χ (fun j => (ternaryCyclicPair M r e t P).eval x (false, (i, j))) = _
    simp only [ternaryCyclicPair, Circuit.eval_bundle, Bool.false_eq_true, ↓reduceIte]
    exact cyclicProduct_twoBlock_correct f χ 3 (by decide) r ψ hψ e he d P hP
      p q hp hq hpq x hx₀ hx₁ i
  have hE (i : Fin (3 ^ r)) : cyclicEval f χ (fun j => y (true, (i, j))) =
      d * ((3 ^ r : ℕ) : S) *
        ((p * q).coeff i.val + χ (3 ^ r • t) * (p * q).coeff (3 ^ r + i.val)) := by
    change cyclicEval f χ (fun j => (ternaryCyclicPair M r e t P).eval x (true, (i, j))) = _
    simp only [ternaryCyclicPair, Circuit.eval_bundle, ↓reduceIte, χ.map_nsmul_eq_pow]
    exact twistedCyclicProduct_twoBlock_correct f χ 3 (by decide) r ψ hψ e t he d P hP
      p q hp hq hpq x hx₀ hx₁ i
  have hrec (i : Fin (3 ^ r)) (b : Bool) :
      cyclicEval f χ (fun j => (ternaryRecoverRows M (3 ^ r) (3 ^ r • t)).eval y (i, (b, j))) =
        d * ((3 ^ (r + 1) : ℕ) : S) * (p * q).coeff (if b then 3 ^ r + i.val else i.val) := by
    have hid := ternaryRecovery_scaled_identity (χ (3 ^ r • t))
      (d * ((3 ^ r : ℕ) : S)) ((p * q).coeff i.val) ((p * q).coeff (3 ^ r + i.val))
      (cyclicEval f χ (fun j => y (false, (i, j))))
      (cyclicEval f χ (fun j => y (true, (i, j)))) hζ (hD i) (hE i)
    have hscale : (3 : S) * (d * ((3 ^ r : ℕ) : S)) = d * ((3 ^ (r + 1) : ℕ) : S) := by
      simp only [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
      ring
    cases b
    · simp only [ternaryRecoverRows, Circuit.eval_bundle, Circuit.eval_comp_function,
        Circuit.eval_wire_function]
      rw [ternaryRecovery_cyclicEval_low]
      simpa only [Bool.false_eq_true, ↓reduceIte, hscale] using hid.1
    · simp only [ternaryRecoverRows, Circuit.eval_bundle, Circuit.eval_comp_function,
        Circuit.eval_wire_function]
      rw [ternaryRecovery_cyclicEval_high]
      simpa only [↓reduceIte, hscale] using hid.2
  by_cases hk : k.val < 3 ^ r
  · have h := hrec ⟨k.val, hk⟩ false
    simpa only [ternaryProduct, Circuit.eval_comp_function, twoBlockJoin,
      Circuit.eval_wire, dif_pos hk, Bool.false_eq_true, ↓reduceIte, y] using h
  · have hk' : k.val - 3 ^ r < 3 ^ r := by have := k.isLt; omega
    have h := hrec ⟨k.val - 3 ^ r, hk'⟩ true
    have hind : 3 ^ r + (k.val - 3 ^ r) = k.val := by omega
    simpa only [ternaryProduct, Circuit.eval_comp_function, twoBlockJoin,
      Circuit.eval_wire, dif_neg hk, ↓reduceIte, hind, y] using h

end
end DivisionFree.Fourier
