-- Prove2me | solution 1 for MagmaMonoid.commutativeImage_eq_diagonalImage_of_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:17:30.971744+00:00
-- url     : https://prove2.me/submissions/4599d5d7-5f73-45d6-892c-bfe2f48eebeb

-- Sol generated from Tropical/MagmaMonoid/Transformation.lean
import Mathlib
import Definitions.Def_Tropical_MagmaMonoid_Transformation

/-!
# The magma monoid as a transformation monoid

A formalization of the pairmorph viewpoint from Baiduk and Kozerenko,
*Transformation Semigroup Perspective on the Magma Monoid* (2026).
-/

open MagmaMonoid































open MagmaMonoid in
theorem solution{X : Type*}
    (f : Operation X) (h : product f f = f) :
    commutativeImage f = diagonalImage f := by
  ext ⟨x, y⟩
  simp [commutativeImage, diagonalImage, pairImage, pairmorph]
  constructor
  · rintro ⟨⟨a, b, hab, hba⟩, rfl⟩
    have hidem : f (f a b) (f b a) = f a b := by
      have hx : product f f a b = f a b := congr_fun (congr_fun h a) b
      simpa [product] using hx
    rw [hab, hba] at hidem
    exact ⟨x, hidem, hidem⟩
  · rintro ⟨z, hz⟩
    exact ⟨⟨z, z, hz.1, hz.2⟩, hz.1.symm.trans hz.2⟩
