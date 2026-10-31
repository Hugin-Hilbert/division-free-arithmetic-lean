import DivisionFree.Fourier.ExtensionProduct
import DivisionFree.Fourier.CyclotomicSplitMap

/-! Correctness interfaces and dimension transport for explicit cyclotomic
multiplication circuits. These interfaces contain no unchecked cost field. -/

namespace DivisionFree.Fourier

universe u

/-- An actual circuit computes a specified natural multiple of the product
in the cyclotomic quotient, over every commutative base ring. -/
def CyclotomicCorrect (m : ℕ) [NeZero m] (d : ℕ)
    (P : Circuit (Bool × ZMod m) (ZMod m)) : Prop :=
  ∀ (R : Type u) [CommRing R] (x : Bool × ZMod m → R),
    toCyclotomic (P.eval x) = (d : CyclotomicRing R m) *
      (toCyclotomic (fun j => x (false, j)) * toCyclotomic (fun j => x (true, j)))

/-- Transport just the dimension of a circuit along an equality. -/
def castCyclotomicCircuit {m n : ℕ} (h : m = n)
    (P : Circuit (Bool × ZMod m) (ZMod m)) :
    Circuit (Bool × ZMod n) (ZMod n) := h ▸ P

@[simp] theorem castCyclotomicCircuit_cost {m n : ℕ} (h : m = n)
    (P : Circuit (Bool × ZMod m) (ZMod m)) :
    (castCyclotomicCircuit h P).cost = P.cost := by
  subst n
  rfl

theorem castCyclotomicCircuit_correct {m n : ℕ} [NeZero m] [NeZero n]
    (h : m = n) (d : ℕ) (P : Circuit (Bool × ZMod m) (ZMod m))
    (hP : CyclotomicCorrect.{u} m d P) :
    CyclotomicCorrect.{u} n d (castCyclotomicCircuit h P) := by
  subst n
  exact hP

theorem cyclicSchoolbook_cyclotomicCorrect (m : ℕ) [NeZero m] :
    CyclotomicCorrect.{u} m 1 (cyclicSchoolbook m) := by
  intro R _ x
  simpa only [toCyclotomic, Nat.cast_one, one_mul] using
    cyclicSchoolbook_correct (AdjoinRoot.of _) (cyclotomicCharacter R m) x

/-- One recursive step on prime-power cyclotomic extensions. -/
theorem extensionProduct_primePower_correct (p q r : ℕ) [NeZero p]
    (hp : p.Prime) (hq : 0 < q) (hqr : r + 1 ≤ q)
    (d : ℕ) (P : Circuit (Bool × ZMod (p ^ q)) (ZMod (p ^ q)))
    (hP : CyclotomicCorrect.{u} (p ^ q) d P) :
    CyclotomicCorrect.{u} (p ^ q * p ^ r) (d * p ^ (r + 1))
      (extensionProduct (p ^ q) (p ^ r) p (NeZero.pos p) (r + 1) P) := by
  intro R _ x
  have hlen : 2 * p ^ r ≤ p ^ (r + 1) := by
    rw [pow_succ]
    exact Nat.mul_le_mul_right (p ^ r) hp.two_le |>.trans_eq (Nat.mul_comm p (p ^ r))
  have hdiv : p ^ (r + 1) ∣ p ^ q := Nat.pow_dvd_pow p hqr
  have h := extensionProduct_correct (p ^ q) (p ^ r) p (NeZero.pos p) (r + 1)
    hlen hdiv (cyclotomicSplitMap p q r hp hq) (AdjoinRoot.of _)
    (cyclotomicRoot R (p ^ q * p ^ r))
    (cyclotomicSplitMap_of p q r hp hq)
    (cyclotomicSplitMap_root p q r hp hq)
    (cyclotomicRoot_pow R (p ^ q * p ^ r)) (d : CyclotomicRing R (p ^ q)) P (hP R) x
  simpa only [toCyclotomic, cyclicEval, cyclotomicCharacter, AddChar.zmodChar_apply,
    map_natCast, Nat.cast_mul, Nat.cast_pow] using h

end DivisionFree.Fourier
