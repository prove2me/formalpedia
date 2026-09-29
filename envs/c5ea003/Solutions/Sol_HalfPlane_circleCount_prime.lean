-- Prove2me | solution 1 for HalfPlane.circleCount_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:55:25.768212+00:00
-- url     : https://prove2.me/submissions/9af8b841-64b9-4def-a24b-b42eda02f434

-- Sol generated from MachineLearning/HalfPlaneCRTSeparable.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCRTSeparable
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Theorems.Thm_HalfPlane_circleCount_prime_int

/-!
# The circle count is CRT-separable

The modular circle `x² + y² ≡ 1 (mod N)` is a *local* object: its point count
splits as a product over coprime factorisations,

  `C(m n) = C(m) · C(n)`  for `gcd(m,n) = 1`,

and at an odd prime it is given by the classical conic count

  `C(p) = p - χ(-1) = p - 1` if `p ≡ 1 (mod 4)`, `p + 1` if `p ≡ 3 (mod 4)`.

The proof of the prime formula is by the stereographic parametrisation of the
conic from the point `(-1, 0)`: the circle minus that point is in bijection with
the set of slopes `t` for which `1 + t² ≠ 0`.

This is the "CRT-separable" baseline against which the half-plane count
`H(N)` of `HalfPlaneReflection.lean` is measured.
-/

open HalfPlane

open Finset


variable {m n : ℕ} [NeZero m] [NeZero n]





variable (p : ℕ) [Fact (Nat.Prime p)]


variable {p}











open HalfPlane in
theorem solution(hp : p ≠ 2) :
    circleCount p = if p % 4 = 1 then p - 1 else p + 1 := by
  have hodd : p % 2 = 1 :=
    Nat.odd_iff.mp ((Fact.out (p := Nat.Prime p)).odd_of_ne_two hp)
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n p]; exact_mod_cast hp
  have hchi : quadraticChar (ZMod p) (-1) = ZMod.χ₄ (Fintype.card (ZMod p)) :=
    quadraticChar_neg_one hchar
  rw [ZMod.card p] at hchi
  have hkey := circleCount_prime_int (p := p) hp
  have hp1 : 1 ≤ p := (Fact.out (p := Nat.Prime p)).one_lt.le
  by_cases h4 : p % 4 = 1
  · have : ZMod.χ₄ (p : ZMod 4) = 1 := by
      rw [ZMod.χ₄_nat_eq_if_mod_four]
      simp [h4]
      omega
    rw [this] at hchi
    rw [hchi] at hkey
    simp only [h4, if_true]
    omega
  · have h3 : p % 4 = 3 := by omega
    have : ZMod.χ₄ (p : ZMod 4) = -1 := by
      rw [ZMod.χ₄_nat_eq_if_mod_four]
      simp [h3]
      omega
    rw [this] at hchi
    rw [hchi] at hkey
    simp only [h4, if_false]
    omega
