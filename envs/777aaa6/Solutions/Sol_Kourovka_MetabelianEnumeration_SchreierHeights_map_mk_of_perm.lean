-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.map_mk_of_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:16:41.928363+00:00
-- url     : https://prove2.me/submissions/a69f8a07-1979-4ad0-b558-67c6df1acc9e

import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
import Definitions.Def_Kourovka_Schreier_PathLifting
import Definitions.Def_Kourovka_Halfspaces_SchreierHeights
import Theorems.Thm_Kourovka_Schreier_Transversal_edge_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_of
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_rewrite_mk
attribute [local simp] Kourovka.Schreier.Transversal.edge_vertex
attribute [local simp] Kourovka.Schreier.Transversal.evaluate_of
attribute [local simp] Kourovka.Schreier.Transversal.rep_rep
attribute [local simp] Kourovka.Schreier.Transversal.rep_vertex
attribute [local simp] Kourovka.Schreier.Transversal.rewrite_mk



set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X Q : Type*} [CommGroup Q]
namespace Kourovka.MetabelianEnumeration.SchreierHeights
theorem _root_.solution (π : FreeGroup X →* Q) {xs ys : List (X × Bool)}
    (h : xs.Perm ys) : π (FreeGroup.mk xs) = π (FreeGroup.mk ys) := by
  rw [FreeGroup.lift_unique π (fun _ => rfl), FreeGroup.lift_unique π (fun _ => rfl)]
  simp only [FreeGroup.lift_mk]
  exact (h.map _).prod_eq
end Kourovka.MetabelianEnumeration.SchreierHeights
