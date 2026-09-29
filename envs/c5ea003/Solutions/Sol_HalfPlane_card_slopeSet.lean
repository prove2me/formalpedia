-- Prove2me | solution 1 for HalfPlane.card_slopeSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:51:22.974429+00:00
-- url     : https://prove2.me/submissions/ae712778-acb0-480a-b125-7bc3db265937

-- Sol generated from MachineLearning/HalfPlaneCRTSeparable.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCRTSeparable
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic

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
    ((slopeSet p).card : ℤ) = p - (quadraticChar (ZMod p) (-1) + 1) := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n p]; exact_mod_cast hp
  have hsplit :
      (Finset.univ.filter (fun t : ZMod p => 1 + t ^ 2 ≠ 0)).card
        + (Finset.univ.filter (fun t : ZMod p => ¬ (1 + t ^ 2 ≠ 0))).card
        = Fintype.card (ZMod p) := by
    simpa using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (ZMod p))) (p := fun t => 1 + t ^ 2 ≠ 0))
  have hroots : (Finset.univ.filter (fun t : ZMod p => ¬ (1 + t ^ 2 ≠ 0)))
      = {x : ZMod p | x ^ 2 = -1}.toFinset := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not,
      Set.mem_toFinset, Set.mem_setOf_eq]
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  have hcard : (({x : ZMod p | x ^ 2 = -1}.toFinset).card : ℤ)
      = quadraticChar (ZMod p) (-1) + 1 :=
    quadraticChar_card_sqrts hchar (-1)
  have hp' : Fintype.card (ZMod p) = p := ZMod.card p
  have : ((slopeSet p).card : ℤ) + (({x : ZMod p | x ^ 2 = -1}.toFinset).card : ℤ)
      = (p : ℤ) := by
    rw [← hcard] at *
    have := hsplit
    rw [hroots, hp'] at this
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) this
  rw [hcard] at this
  linarith
