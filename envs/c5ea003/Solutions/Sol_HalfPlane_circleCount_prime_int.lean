-- Prove2me | solution 1 for HalfPlane.circleCount_prime_int
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:54:07.103598+00:00
-- url     : https://prove2.me/submissions/8b15cd0c-207c-4c3e-b4eb-73f776d06d0b

-- Sol generated from MachineLearning/HalfPlaneCRTSeparable.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCRTSeparable
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Theorems.Thm_HalfPlane_card_circleZ_erase
import Theorems.Thm_HalfPlane_card_slopeSet
import Theorems.Thm_HalfPlane_circleCount_eq_card_circleZ
import Theorems.Thm_HalfPlane_mem_circleZ

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
    (circleCount p : ℤ) = (p : ℤ) - quadraticChar (ZMod p) (-1) := by
  have hmem : ((-1 : ZMod p), (0 : ZMod p)) ∈ circleZ p := by
    rw [mem_circleZ]; ring
  have hcard : (circleZ p).card
      = ((circleZ p).erase ((-1 : ZMod p), (0 : ZMod p))).card + 1 := by
    rw [Finset.card_erase_of_mem hmem]
    have : 1 ≤ (circleZ p).card := Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  rw [circleCount_eq_card_circleZ, hcard, card_circleZ_erase hp]
  push_cast
  rw [card_slopeSet hp]
  ring
