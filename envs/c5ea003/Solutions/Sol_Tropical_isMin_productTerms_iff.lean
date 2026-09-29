-- Prove2me | solution 1 for Tropical.isMin_productTerms_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T04:02:40.810791+00:00
-- url     : https://prove2.me/submissions/9eec9e54-0372-4bb9-a136-5fa89a490d8c

import Mathlib
import Definitions.Def_Tropical_CornerLocusProduct
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Data.Fintype.Basic
open Tropical in
theorem solution {X α I J : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
    (f : I → X → α) (g : J → X → α) (x : X) (i : I) (j : J) :
    Tropical.IsMin (productTerms f g) x (i, j) ↔ Tropical.IsMin f x i ∧ Tropical.IsMin g x j := by
  simp only [Tropical.IsMin, productTerms, Prod.forall]
  constructor
  · -- freeze one factor at its own index and cancel it
    intro h
    exact ⟨fun k => le_of_add_le_add_right (h k j), fun l => le_of_add_le_add_left (h i l)⟩
  · rintro ⟨hf, hg⟩ k l
    exact add_le_add (hf k) (hg l)
