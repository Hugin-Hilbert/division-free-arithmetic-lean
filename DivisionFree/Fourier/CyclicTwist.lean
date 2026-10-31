import DivisionFree.Fourier.CyclicProductResources
import DivisionFree.Circuit.Evaluation

/-! Twisting each Fourier input coefficient by a root power is a wiring
operation in the cyclic coefficient representation. -/

namespace DivisionFree.Fourier

noncomputable section

variable (M : ℕ) [NeZero M]

/-- Multiply row `k` by the represented root to the power `k*e`. -/
def rowTwist (n : ℕ) (e : ZMod M) :
    Circuit (Fin n × ZMod M) (Fin n × ZMod M) :=
  .wire fun j => (j.1, j.2 - j.1.val • e)

/-- Apply the same twist to both input polynomials. -/
def inputTwist (n : ℕ) (e : ZMod M) :
    Circuit (Bool × (Fin n × ZMod M)) (Bool × (Fin n × ZMod M)) :=
  .wire fun j => (j.1, j.2.1, j.2.2 - j.2.1.val • e)

omit [NeZero M] in
@[simp] theorem rowTwist_cost (n : ℕ) (e : ZMod M) : (rowTwist M n e).cost = 0 := rfl
omit [NeZero M] in
@[simp] theorem rowTwist_multiplications (n : ℕ) (e : ZMod M) :
    (rowTwist M n e).multiplications = 0 := rfl
omit [NeZero M] in
@[simp] theorem rowTwist_constantBits (n : ℕ) (e : ZMod M) :
    (rowTwist M n e).constantBits = 0 := rfl
omit [NeZero M] in
@[simp] theorem inputTwist_cost (n : ℕ) (e : ZMod M) :
    (inputTwist M n e).cost = 0 := rfl
omit [NeZero M] in
@[simp] theorem inputTwist_multiplications (n : ℕ) (e : ZMod M) :
    (inputTwist M n e).multiplications = 0 := rfl
omit [NeZero M] in
@[simp] theorem inputTwist_constantBits (n : ℕ) (e : ZMod M) :
    (inputTwist M n e).constantBits = 0 := rfl

theorem rowTwist_correct {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (χ : AddChar (ZMod M) S) (n : ℕ) (e : ZMod M)
    (x : Fin n × ZMod M → R) (k : Fin n) :
    cyclicEval f χ (fun j => (rowTwist M n e).eval x (k, j)) =
      χ e ^ k.val * cyclicEval f χ (fun j => x (k, j)) := by
  change cyclicEval f χ (fun j => x (k, j - k.val • e)) = _
  simpa only [χ.map_nsmul_eq_pow] using
    cyclicEval_shift f χ (k.val • e) (fun j => x (k, j))

theorem inputTwist_correct {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (χ : AddChar (ZMod M) S) (n : ℕ) (e : ZMod M)
    (x : Bool × (Fin n × ZMod M) → R) (b : Bool) (k : Fin n) :
    cyclicEval f χ (fun j => (inputTwist M n e).eval x (b, (k, j))) =
      χ e ^ k.val * cyclicEval f χ (fun j => x (b, (k, j))) := by
  change cyclicEval f χ (fun j => x (b, (k, j - k.val • e))) = _
  simpa only [χ.map_nsmul_eq_pow] using
    cyclicEval_shift f χ (k.val • e) (fun j => x (b, (k, j)))

/-- A length-`s^r` cyclic product with input twisting and output untwisting.
The twists only permute already available base-ring coefficients. -/
def twistedCyclicProduct (s : ℕ) (hs : 0 < s) (r : ℕ) [NeZero (s ^ r)]
    (e t : ZMod M) (P : Circuit (Bool × ZMod M) (ZMod M)) :
    Circuit (Bool × (Fin (s ^ r) × ZMod M)) (Fin (s ^ r) × ZMod M) :=
  .comp (inputTwist M (s ^ r) t)
    (.comp (cyclicProduct M s hs r e P) (rowTwist M (s ^ r) (-t)))

theorem twistedCyclicProduct_cost (s : ℕ) (hs : 0 < s) (r : ℕ)
    [NeZero (s ^ r)] (e t : ZMod M) (P : Circuit (Bool × ZMod M) (ZMod M)) :
    (twistedCyclicProduct M s hs r e t P).cost =
      3 * M * s * r * s ^ r + s ^ r * P.cost := by
  simp [twistedCyclicProduct, cyclicProduct_cost]

theorem twistedCyclicProduct_multiplications (s : ℕ) (hs : 0 < s) (r : ℕ)
    [NeZero (s ^ r)] (e t : ZMod M) (P : Circuit (Bool × ZMod M) (ZMod M)) :
    (twistedCyclicProduct M s hs r e t P).multiplications =
      s ^ r * P.multiplications := by
  simp [twistedCyclicProduct, cyclicProduct_multiplications]

theorem twistedCyclicProduct_constantBits (s : ℕ) (hs : 0 < s) (r : ℕ)
    [NeZero (s ^ r)] (e t : ZMod M) (P : Circuit (Bool × ZMod M) (ZMod M)) :
    (twistedCyclicProduct M s hs r e t P).constantBits =
      s ^ r * P.constantBits := by
  simp [twistedCyclicProduct, cyclicProduct_constantBits]

end
end DivisionFree.Fourier
