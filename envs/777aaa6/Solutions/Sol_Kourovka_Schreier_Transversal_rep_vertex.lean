-- Prove2me | solution 1 for Kourovka.Schreier.Transversal.rep_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:42:21.205388+00:00
-- url     : https://prove2.me/submissions/a4d10731-a4fc-458f-ab1d-4a91fd32cfc0

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic
import Definitions.Def_Kourovka_Schreier_Transversal
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
attribute [local simp] Kourovka.Schreier.Transversal.rep_rep

set_option autoImplicit true
open Kourovka Kourovka.Schreier
variable {X : Type*}
open Kourovka.Schreier.Transversal
variable {L : Subgroup (FreeGroup X)} (S : Transversal L)
namespace Kourovka.Schreier.Transversal
theorem _root_.solution (v : S.vertices) : S.rep v.val = v.val := by
  obtain ⟨w, hw⟩ := v.property
  rw [← hw, S.rep_rep]
end Kourovka.Schreier.Transversal
