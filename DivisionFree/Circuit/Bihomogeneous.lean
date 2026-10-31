import DivisionFree.Circuit.CoefficientEval
import DivisionFree.Polynomial.MixedCoefficients

/-! Bihomogeneous circuit inputs and extraction of the mixed coefficient. -/

namespace DivisionFree.Circuit

open DivisionFree.PolynomialArithmetic

universe u

/-- A circuit that is homogeneous of degree one in each of its input blocks. -/
def Bihomogeneous.{v} {n m r : ℕ} (C : Circuit (Fin n ⊕ Fin m) (Fin r)) : Prop :=
  ∀ (R : Type v) [CommRing R]
    (a : Fin n → R) (b : Fin m → R) (s t : R),
    C.eval (Sum.elim (fun i => s * a i) (fun j => t * b j)) =
      fun k => s * t * C.eval (Sum.elim a b) k

/-- Put the left block in the inner degree-one direction and the right block
in the outer degree-one direction. -/
noncomputable def bilinearInput {R : Type u} [CommRing R] {n m : ℕ}
    (a : Fin n → R) (b : Fin m → R) :
    Fin n ⊕ Fin m → Polynomial (Polynomial R) :=
  Sum.elim (fun i => Polynomial.C (Polynomial.C (a i) * Polynomial.X))
    (fun j => Polynomial.C (Polynomial.C (b j)) * Polynomial.X)

theorem bilinearInput_coeff00 {R : Type u} [CommRing R] {n m : ℕ}
    (a : Fin n → R) (b : Fin m → R) :
    (fun i => coeff00 (bilinearInput a b i)) = fun _ => 0 := by
  funext i
  cases i with
  | inl i => simp [bilinearInput, coeff00]
  | inr j => simp [bilinearInput, coeff00]

theorem bilinearInput_coeff10 {R : Type u} [CommRing R] {n m : ℕ}
    (a : Fin n → R) (b : Fin m → R) :
    (fun i => coeff10 (bilinearInput a b i)) = Sum.elim a (fun _ => 0) := by
  funext i
  cases i with
  | inl i => simp [bilinearInput, coeff10]
  | inr j => simp [bilinearInput, coeff10]

theorem bilinearInput_coeff01 {R : Type u} [CommRing R] {n m : ℕ}
    (a : Fin n → R) (b : Fin m → R) :
    (fun i => coeff01 (bilinearInput a b i)) = Sum.elim (fun _ => 0) b := by
  funext i
  cases i with
  | inl i => simp [bilinearInput, coeff01]
  | inr j => simp [bilinearInput, coeff01]

theorem bilinearInput_coeff11 {R : Type u} [CommRing R] {n m : ℕ}
    (a : Fin n → R) (b : Fin m → R) :
    (fun i => coeff11 (bilinearInput a b i)) = fun _ => 0 := by
  funext i
  cases i with
  | inl i => simp [bilinearInput, coeff11]
  | inr j => simp [bilinearInput, coeff11]

private noncomputable def constantEmbed {R : Type u} [CommRing R] :
    R →+* Polynomial (Polynomial R) :=
  (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)).comp
    (Polynomial.C : R →+* Polynomial R)

theorem coeff11_of_bihomogeneous {n m r : ℕ}
    (C : Circuit (Fin n ⊕ Fin m) (Fin r)) (hC : Bihomogeneous.{u} C)
    {R : Type u} [CommRing R] (a : Fin n → R) (b : Fin m → R) (k : Fin r) :
    coeff11 (C.eval (bilinearInput a b) k) = C.eval (Sum.elim a b) k := by
  let s : Polynomial (Polynomial R) := Polynomial.C Polynomial.X
  let t : Polynomial (Polynomial R) := Polynomial.X
  have hinput :
      Sum.elim (fun i => s * constantEmbed (a i))
        (fun j => t * constantEmbed (b j)) = bilinearInput a b := by
    funext i
    cases i with
    | inl i =>
        change Polynomial.C Polynomial.X *
          Polynomial.C (Polynomial.C (a i)) =
            Polynomial.C (Polynomial.C (a i) * Polynomial.X)
        calc
          Polynomial.C Polynomial.X * Polynomial.C (Polynomial.C (a i)) =
              Polynomial.C (Polynomial.X * Polynomial.C (a i)) :=
            Polynomial.C_mul.symm
          _ = Polynomial.C (Polynomial.C (a i) * Polynomial.X) := by
            rw [mul_comm]
    | inr j =>
        change Polynomial.X * Polynomial.C (Polynomial.C (b j)) =
          Polynomial.C (Polynomial.C (b j)) * Polynomial.X
        exact mul_comm _ _
  have hhom := hC (R := Polynomial (Polynomial R))
    (a := fun i => constantEmbed (a i)) (b := fun j => constantEmbed (b j))
    (s := s) (t := t)
  have hhomAt := congrFun hhom k
  have hhomAt' : C.eval (bilinearInput a b) k =
      s * t * C.eval (Sum.elim (fun i => constantEmbed (a i))
        (fun j => constantEmbed (b j))) k := by
    simpa only [hinput] using hhomAt
  have heval := eval_map constantEmbed C (Sum.elim a b) k
  have hbase : (fun i => constantEmbed (Sum.elim a b i)) =
      Sum.elim (fun i => constantEmbed (a i)) (fun j => constantEmbed (b j)) := by
    funext i
    cases i <;> rfl
  rw [hbase] at heval
  have hs00 : coeff00 s = 0 := by simp [s, coeff00]
  have hs10 : coeff10 s = 1 := by simp [s, coeff10]
  have hs01 : coeff01 s = 0 := by simp [s, coeff01]
  have hs11 : coeff11 s = 0 := by
    simp [s, coeff11]
  have ht00 : coeff00 t = 0 := by simp [t, coeff00]
  have ht10 : coeff10 t = 0 := by simp [t, coeff10]
  have ht01 : coeff01 t = 1 := by simp [t, coeff01]
  have ht11 : coeff11 t = 0 := by
    change ((Polynomial.X : Polynomial (Polynomial R)).coeff 1).coeff 1 = 0
    rw [Polynomial.coeff_X_one]
    exact Polynomial.coeff_C_of_ne_zero (by decide)
  have hst00 : coeff00 (s * t) = 0 := by
    rw [coeff00_mul, hs00, ht00]
    ring
  have hst10 : coeff10 (s * t) = 0 := by
    rw [coeff10_mul, hs00, hs10, ht00, ht10]
    ring
  have hst01 : coeff01 (s * t) = 0 := by
    rw [coeff01_mul, hs00, hs01, ht00, ht01]
    ring
  have hst11 : coeff11 (s * t) = 1 := by
    rw [coeff11_mul, hs00, hs10, hs01, hs11, ht00, ht10, ht01, ht11]
    ring
  have hc00 (c : R) : coeff00 (constantEmbed c) = c := by simp [constantEmbed, coeff00]
  have hc10 (c : R) : coeff10 (constantEmbed c) = 0 := by simp [constantEmbed, coeff10]
  have hc01 (c : R) : coeff01 (constantEmbed c) = 0 := by simp [constantEmbed, coeff01]
  have hc11 (c : R) : coeff11 (constantEmbed c) = 0 := by simp [constantEmbed, coeff11]
  calc
    coeff11 (C.eval (bilinearInput a b) k) =
        coeff11 (s * t * C.eval (Sum.elim (fun i => constantEmbed (a i))
          (fun j => constantEmbed (b j))) k) := by rw [hhomAt']
    _ = coeff11 (s * t * constantEmbed (C.eval (Sum.elim a b) k)) := by
      rw [← heval]
    _ = C.eval (Sum.elim a b) k := by
      rw [coeff11_mul, hst00, hst10, hst01, hst11]
      rw [hc11, hc01, hc10, hc00]
      ring

end DivisionFree.Circuit
