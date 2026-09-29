-- Prove2me | solution 1 for MagmaMonoid.product_self_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:17:32.562897+00:00
-- url     : https://prove2.me/submissions/027e55df-bce9-4d46-8cb3-8670803450f5

-- Sol generated from Tropical/MagmaMonoid/Transformation.lean
import Mathlib
import Definitions.Def_Tropical_MagmaMonoid_Transformation

/-!
# The magma monoid as a transformation monoid

A formalization of the pairmorph viewpoint from Baiduk and Kozerenko,
*Transformation Semigroup Perspective on the Magma Monoid* (2026).
-/

open MagmaMonoid















/-- Pairmorph converts the magma product into composition of transformations. -/
theorem pairmorph_product {X : Type*} (f g : Operation X) :
    pairmorph (product f g) = pairmorph g ∘ pairmorph f := by
  funext p
  simp [product, pairmorph]
















open MagmaMonoid in
theorem solution{X : Type*} (f : Operation X) :
    product f f = f ↔ ∀ p ∈ pairImage f, pairmorph f p = p := by
  constructor
  · intro h p hp
    obtain ⟨q, rfl⟩ := hp
    have : pairmorph f (pairmorph f q) = (pairmorph f ∘ pairmorph f) q := rfl
    rw [this, ← pairmorph_product, h]
  · intro h
    funext a b
    have hp : (f a b, f b a) ∈ pairImage f := ⟨(a, b), rfl⟩
    have hf := h (f a b, f b a) hp
    simp [pairmorph] at hf
    exact hf.1
