-- Prove2me | solution 1 for MagmaMonoid.exists_pairmorph_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:17:32.110544+00:00
-- url     : https://prove2.me/submissions/fa6bd996-cab6-49c8-8be0-c423efb58652

-- Sol generated from Tropical/MagmaMonoid/Transformation.lean
import Mathlib
import Definitions.Def_Tropical_MagmaMonoid_Transformation

/-!
# The magma monoid as a transformation monoid

A formalization of the pairmorph viewpoint from Baiduk and Kozerenko,
*Transformation Semigroup Perspective on the Magma Monoid* (2026).
-/

open MagmaMonoid
















/-- Every pairmorph transformation commutes with pair reversal. -/
theorem pairmorph_commutes {X : Type*} (f : Operation X) :
    IsPairmorph (pairmorph f) := by
  simp [IsPairmorph, Function.Commute, Function.Semiconj]
  intro a b
  rfl















open MagmaMonoid in
theorem solution{X : Type*} (T : X × X → X × X) :
    (∃ f : Operation X, pairmorph f = T) ↔ IsPairmorph T := by
  constructor
  · intro ⟨f, hf⟩
    rw [hf.symm]
    exact pairmorph_commutes f
  · intro hT
    use fun a b => (T (a, b)).1
    funext p
    simp only [pairmorph]
    have h := hT p
    simp only [swap] at h
    rw [h]
