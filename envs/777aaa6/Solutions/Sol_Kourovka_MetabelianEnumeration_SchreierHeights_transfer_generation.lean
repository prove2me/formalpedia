-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.transfer_generation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:21:57.902282+00:00
-- url     : https://prove2.me/submissions/4c7319f1-349e-4408-abd2-cf88998a7f5c

import Definitions.Def_Kourovka_Halfspaces_SchreierPaths
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeneration

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry HalfspaceSplitting HalfspaceLoops
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X L : Type} [AddCommGroup L] [DecidableEq X]
namespace Kourovka.MetabelianEnumeration.SchreierHeights
theorem _root_.solution {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (s : Set G) (t : Set H) (hs : Subgroup.closure s = ⊤)
    (ht : ∀ x ∈ s, e x ∈ t) : Subgroup.closure t = ⊤ := by
  have hmap : Subgroup.closure (e '' s) = ⊤ := by
    change Subgroup.closure (e.toMonoidHom '' s) = ⊤
    rw [← MonoidHom.map_closure e.toMonoidHom, hs,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  apply top_unique
  rw [← hmap]
  apply Subgroup.closure_mono
  rintro _ ⟨x, hx, rfl⟩
  exact ht x hx
end Kourovka.MetabelianEnumeration.SchreierHeights
