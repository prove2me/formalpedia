-- Prove2me | solution 1 for MagmaMonoid.commutativeImage_eq_diagonalImage_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:17:31.608734+00:00
-- url     : https://prove2.me/submissions/ca1b88cd-4b72-4cd0-a290-87f262552af0

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
    (f : Operation X) (h : IsRegular f) :
    commutativeImage f = diagonalImage f := by
  obtain ⟨g, hreg⟩ := h
  ext ⟨x, y⟩
  simp [commutativeImage, diagonalImage, pairImage, pairmorph]
  constructor
  · rintro ⟨⟨a, b, hab, hba⟩, rfl⟩
    have hx : f (g x x) (g x x) = x := by
      have heq : product (product f g) f a b = f a b :=
        congr_fun (congr_fun hreg a) b
      simpa [product, hab, hba] using heq
    exact ⟨g x x, hx, hx⟩
  · rintro ⟨z, hz⟩
    exact ⟨⟨z, z, hz.1, hz.2⟩, hz.1.symm.trans hz.2⟩
