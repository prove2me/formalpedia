-- Prove2me | solution 1 for Cryptography.IsogenySIDH.radicalTwoEval_fiber_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:24:50.963808+00:00
-- url     : https://prove2.me/submissions/785d5f9f-a031-4cce-b69b-6458117709be

-- Sol generated from Cryptography/IsogenySIDH/DeepRadicalMontgomery.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_DeepRadicalMontgomery
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomery
import Theorems.Thm_Cryptography_IsogenySIDH_quotient_fiber_classification
import Theorems.Thm_Cryptography_IsogenySIDH_radicalTwoEval_deck_invariant
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










open Cryptography.IsogenySIDH in
theorem solution{x y z w : K}
    (hx : x ≠ 0) (hz : z ≠ 0) (hbranch : x ^ 2 ≠ 1) :
    radicalTwoEval (x, y) = radicalTwoEval (z, w) ↔
      (z = x ∧ w = y) ∨ (z = x⁻¹ ∧ w = -(y * x⁻¹ ^ 2)) := by
  have hc : 1 - x⁻¹ ^ 2 ≠ 0 := by
    intro hc
    apply hbranch
    field_simp [hx] at hc ⊢
    linear_combination hc
  constructor
  · intro h
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    dsimp [radicalTwoEval] at hfst hsnd
    rcases quotient_fiber_classification hx hz hfst with heq | hprod
    · left
      subst z
      exact ⟨rfl, mul_right_cancel₀ hc hsnd.symm⟩
    · right
      have hzx : z = x⁻¹ := by
        apply (mul_left_cancel₀ hx)
        rw [mul_inv_cancel₀ hx]
        exact hprod
      subst z
      refine ⟨rfl, ?_⟩
      apply mul_right_cancel₀ hc
      field_simp [hx] at hsnd ⊢
      linear_combination hsnd
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (radicalTwoEval_deck_invariant hx).symm
