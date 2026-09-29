-- Prove2me | solution 1 for Cryptography.IsogenySIDH.radicalTwoEval_exact_two_fiber
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:26:15.991081+00:00
-- url     : https://prove2.me/submissions/16bd5663-5b88-4418-8e1e-ae1bcc2514c6

-- Sol generated from Cryptography/IsogenySIDH/DeepRadicalMontgomery.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_DeepRadicalMontgomery
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomery
import Theorems.Thm_Cryptography_IsogenySIDH_radicalTwoEval_deck_invariant
import Theorems.Thm_Cryptography_IsogenySIDH_radicalTwoEval_fiber_iff
/-
# Exact fibers of the radical Montgomery 2-isogeny

This file strengthens `RadicalMontgomery` from correctness and an
`X`-coordinate fiber calculation to a classification of the complete affine
fibers away from the kernel and ramification locus.  The nontrivial point in a
fiber is the explicit deck transform

`(x,y) ↦ (x⁻¹, -(y*x⁻²))`.

The results also verify that this transform preserves the source Montgomery
curve and is an involution wherever the rational formulas are defined.
-/

open Cryptography.IsogenySIDH


variable {K : Type*} [Field K]


/-- The deck transformation preserves the source Montgomery equation away
from its pole. -/
theorem radicalTwoDeck_on_curve {A x y : K} (hx : x ≠ 0)
    (hP : OnMontgomery A (x, y)) :
    OnMontgomery A (radicalTwoDeck (x, y)) := by
  dsimp [OnMontgomery] at hP
  dsimp [OnMontgomery, radicalTwoDeck]
  field_simp
  linear_combination hP


/-- Quotient evaluation is constant on the orbit of the deck involution. -/
theorem radicalTwoEval_deck (x y : K) (hx : x ≠ 0) :
    radicalTwoEval (radicalTwoDeck (x, y)) = radicalTwoEval (x, y) := by
  exact radicalTwoEval_deck_invariant hx


/-- Off the ramification locus, the deck mate is genuinely different from the
original affine point. -/
theorem radicalTwoDeck_ne {x y : K} (hx : x ≠ 0) (hbranch : x ^ 2 ≠ 1) :
    radicalTwoDeck (x, y) ≠ (x, y) := by
  intro h
  have hxcoord := congrArg Prod.fst h
  dsimp [radicalTwoDeck] at hxcoord
  apply hbranch
  calc
    x ^ 2 = x * x := by ring
    _ = 1 := by
      nth_rewrite 2 [← hxcoord]
      exact mul_inv_cancel₀ hx




open Cryptography.IsogenySIDH in
theorem solution{A x y z w : K}
    (hx : x ≠ 0) (hbranch : x ^ 2 ≠ 1)
    (hP : OnMontgomery A (x, y)) (hz : z ≠ 0) :
    (OnMontgomery A (radicalTwoDeck (x, y)) ∧
      radicalTwoDeck (x, y) ≠ (x, y)) ∧
    (radicalTwoEval (z, w) = radicalTwoEval (x, y) ↔
      (z, w) = (x, y) ∨ (z, w) = radicalTwoDeck (x, y)) := by
  constructor
  · exact ⟨radicalTwoDeck_on_curve hx hP, radicalTwoDeck_ne hx hbranch⟩
  · constructor
    · intro h
      rcases (radicalTwoEval_fiber_iff hx hz hbranch).mp h.symm with h | h
      · left
        exact Prod.ext h.1 h.2
      · right
        exact Prod.ext h.1 h.2
    · intro h
      rcases h with h | h
      · exact congrArg radicalTwoEval h
      · rw [h]
        exact radicalTwoEval_deck x y hx
