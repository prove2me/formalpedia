-- Prove2me | solution 1 for Tropical.isCorner_productTerms_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T05:46:46.55232+00:00
-- url     : https://prove2.me/submissions/0e404cf8-ae6b-456b-bb2d-18d0ce22c8cf

import Mathlib
import Definitions.Def_Tropical_CornerLocusProduct
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Data.Fintype.Basic
open Tropical in
theorem solution {X α I J : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
    (f : I → X → α) (g : J → X → α) (x : X)
    (hf : ∃ i, Tropical.IsMin f x i) (hg : ∃ j, Tropical.IsMin g x j) :
    IsCorner (productTerms f g) x ↔ IsCorner f x ∨ IsCorner g x := by
  -- a product term is minimal iff both factors are
  have hprod : ∀ i j, Tropical.IsMin (productTerms f g) x (i, j) ↔
      Tropical.IsMin f x i ∧ Tropical.IsMin g x j := by
    intro i j
    simp only [Tropical.IsMin, productTerms, Prod.forall]
    constructor
    · intro h
      exact ⟨fun k => le_of_add_le_add_right (h k j), fun l => le_of_add_le_add_left (h i l)⟩
    · rintro ⟨h1, h2⟩ k l
      exact add_le_add (h1 k) (h2 l)
  constructor
  · -- two distinct minimal pairs differ in one coordinate
    rintro ⟨⟨i, j⟩, ⟨i', j'⟩, hne, h1, h2⟩
    rw [hprod] at h1 h2
    by_cases hii : i = i'
    · right
      refine ⟨j, j', fun h => hne ?_, h1.2, h2.2⟩
      rw [hii, h]
    · left
      exact ⟨i, i', hii, h1.1, h2.1⟩
  · -- pair a corner of one factor with a minimiser of the other
    rintro (⟨i, i', hii, h1, h2⟩ | ⟨j, j', hjj, h1, h2⟩)
    · obtain ⟨j, hj⟩ := hg
      exact ⟨(i, j), (i', j), fun h => hii (Prod.ext_iff.mp h).1,
        (hprod i j).mpr ⟨h1, hj⟩, (hprod i' j).mpr ⟨h2, hj⟩⟩
    · obtain ⟨i, hi⟩ := hf
      exact ⟨(i, j), (i, j'), fun h => hjj (Prod.ext_iff.mp h).2,
        (hprod i j).mpr ⟨hi, h1⟩, (hprod i j').mpr ⟨hi, h2⟩⟩
