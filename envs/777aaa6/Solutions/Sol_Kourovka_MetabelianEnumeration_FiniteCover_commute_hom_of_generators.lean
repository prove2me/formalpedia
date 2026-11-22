-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.commute_hom_of_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:06:22.660179+00:00
-- url     : https://prove2.me/submissions/47343f2e-aeed-4519-b7fd-ae678d784df5

import Definitions.Def_Kourovka_Collection_CollectionRadius
import Definitions.Def_Kourovka_Covers_CertifiedRadius
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverSoundness

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover
theorem _root_.solution {H : Type*} [Group H] (f : G →* H) (S : Set G)
    (hS : Subgroup.closure S = ⊤)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, Commute (f x) (f y)) :
    ∀ x y : G, Commute (f x) (f y) := by
  have hfirst : ∀ x ∈ S, ∀ y : G, Commute (f x) (f y) := by
    intro x hx y
    have hle : Subgroup.closure S ≤ (Subgroup.centralizer {f x}).comap f := by
      apply (Subgroup.closure_le _).mpr
      intro z hz
      change ∀ w ∈ ({f x} : Set H), w * f z = f z * w
      intro w hw
      rcases Set.mem_singleton_iff.mp hw with rfl
      exact hpair x hx z hz
    have hy := hle (show y ∈ Subgroup.closure S by rw [hS]; trivial)
    exact hy (f x) (Set.mem_singleton _)
  intro x y
  have hle : Subgroup.closure S ≤ (Subgroup.centralizer {f y}).comap f := by
    apply (Subgroup.closure_le _).mpr
    intro z hz
    change ∀ w ∈ ({f y} : Set H), w * f z = f z * w
    intro w hw
    rcases Set.mem_singleton_iff.mp hw with rfl
    exact (hfirst z hz y).symm
  have hx := hle (show x ∈ Subgroup.closure S by rw [hS]; trivial)
  exact (hx (f y) (Set.mem_singleton _)).symm
end Kourovka.MetabelianEnumeration.FiniteCover
