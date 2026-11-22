-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.generatorWord_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:20:57.147182+00:00
-- url     : https://prove2.me/submissions/bb0940dc-97ea-46a5-bd7a-d073232c12c3

import Definitions.Def_Kourovka_Halfspaces_SchreierKernel
import Definitions.Def_Kourovka_Halfspaces_SchreierPaths
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_schreierKernelEquiv_of
import Theorems.Thm_Kourovka_Schreier_Transversal_edge_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_of
import Theorems.Thm_Kourovka_Schreier_Transversal_presentationEquiv_of
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_rewrite_mk
attribute [local simp] Kourovka.MetabelianEnumeration.SchreierHeights.schreierKernelEquiv_of
attribute [local simp] Kourovka.Schreier.Transversal.edge_vertex
attribute [local simp] Kourovka.Schreier.Transversal.evaluate_of
attribute [local simp] Kourovka.Schreier.Transversal.presentationEquiv_of
attribute [local simp] Kourovka.Schreier.Transversal.rep_rep
attribute [local simp] Kourovka.Schreier.Transversal.rep_vertex
attribute [local simp] Kourovka.Schreier.Transversal.rewrite_mk



set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X : Type*}
namespace Kourovka.MetabelianEnumeration.SchreierHeights
theorem _root_.solution [DecidableEq X] {L : Subgroup (FreeGroup X)}
    (S : Transversal L) (z : S.Edge) :
    FreeGroup.mk (generatorWord S z) = S.edgeValue z := by
  simp only [generatorWord, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, FreeGroup.mk_toWord]
  rfl
end Kourovka.MetabelianEnumeration.SchreierHeights
