-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.value_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:16:33.094398+00:00
-- url     : https://prove2.me/submissions/41e68cb0-5773-4305-a3d7-21d7a3ad17fe

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
theorem _root_.solution (θ : FreeGroup X →* Multiplicative ℝ) (xs : List (X × Bool)) :
    value θ (FreeGroup.mk xs) = (xs.map (letterHeight fun x => value θ (FreeGroup.of x))).sum := by
  induction xs with
  | nil => exact value_one θ
  | cons z xs ih =>
    rcases z with ⟨x, b⟩
    cases b <;> simp [mk_cons_false, mk_cons_true, letterHeight, ih]
end Kourovka.MetabelianEnumeration.SchreierHeights
