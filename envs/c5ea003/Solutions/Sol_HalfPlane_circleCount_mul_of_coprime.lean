-- Prove2me | solution 1 for HalfPlane.circleCount_mul_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:54:06.372121+00:00
-- url     : https://prove2.me/submissions/8fe843f7-828a-4e73-8c5e-acb2f0578450

-- Sol generated from MachineLearning/HalfPlaneCRTSeparable.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCRTSeparable
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Theorems.Thm_HalfPlane_card_circleZ_mul_of_coprime
import Theorems.Thm_HalfPlane_circleCount_eq_card_circleZ

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
theorem solution(h : Nat.Coprime m n) :
    circleCount (m * n) = circleCount m * circleCount n := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  rw [circleCount_eq_card_circleZ, circleCount_eq_card_circleZ,
    circleCount_eq_card_circleZ, card_circleZ_mul_of_coprime h]
