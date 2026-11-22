-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceSplitting.abelian_twist_collapse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:13:31.351179+00:00
-- url     : https://prove2.me/submissions/8f94ab6d-7407-4d06-9fe1-c8f95b2c071d

import Definitions.Def_Kourovka_Modules_ModuleRealization
import Mathlib.GroupTheory.HNNExtension
import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceSplitting_not_commute_twist

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceSplitting
variable {N : Type*} [Group N]
namespace Kourovka.MetabelianEnumeration.HalfspaceSplitting
theorem _root_.solution (C A B : Subgroup N)
    (habelian : ∀ a b : N, Commute a b) (f : N →* Twist C)
    (hA : ∀ a ∈ A, f a = left C a) (hB : ∀ b ∈ B, f b = right C b) :
    A ≤ C ∨ B ≤ C := by
  by_contra! h
  obtain ⟨a, ha, hac⟩ := Set.not_subset.mp h.1
  obtain ⟨b, hb, hbc⟩ := Set.not_subset.mp h.2
  apply not_commute_twist C hac hbc
  simpa only [hA a ha, hB b hb] using (habelian a b).map f
end Kourovka.MetabelianEnumeration.HalfspaceSplitting
