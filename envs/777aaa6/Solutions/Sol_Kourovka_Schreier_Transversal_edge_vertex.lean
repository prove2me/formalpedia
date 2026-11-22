-- Prove2me | solution 1 for Kourovka.Schreier.Transversal.edge_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:43:08.520186+00:00
-- url     : https://prove2.me/submissions/6816026f-b0c6-4cfc-8dfe-3d9877f7f7ad

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic
import Definitions.Def_Kourovka_Schreier_Transversal
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_vertex
attribute [local simp] Kourovka.Schreier.Transversal.rep_rep
attribute [local simp] Kourovka.Schreier.Transversal.rep_vertex

set_option autoImplicit true
open Kourovka Kourovka.Schreier
variable {X : Type*}
open Kourovka.Schreier.Transversal
variable {L : Subgroup (FreeGroup X)} (S : Transversal L)
namespace Kourovka.Schreier.Transversal
theorem _root_.solution (z : S.Edge) : S.edge z.1.val z.2 = z := by
  apply Prod.ext
  · exact Subtype.ext (S.rep_vertex z.1)
  · rfl
end Kourovka.Schreier.Transversal
