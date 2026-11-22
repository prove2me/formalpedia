-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.schreierKernelEquiv_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:19:57.609606+00:00
-- url     : https://prove2.me/submissions/7c8ff34c-c7ca-4111-bf3d-5d56a20ddada

import Definitions.Def_Kourovka_Halfspaces_HalfspaceRelators
import Definitions.Def_Kourovka_Halfspaces_SchreierKernel
import Theorems.Thm_Kourovka_Schreier_Transversal_edge_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_of
import Theorems.Thm_Kourovka_Schreier_Transversal_presentationEquiv_of
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_rewrite_mk
attribute [local simp] Kourovka.Schreier.Transversal.edge_vertex
attribute [local simp] Kourovka.Schreier.Transversal.evaluate_of
attribute [local simp] Kourovka.Schreier.Transversal.presentationEquiv_of
attribute [local simp] Kourovka.Schreier.Transversal.rep_rep
attribute [local simp] Kourovka.Schreier.Transversal.rep_vertex
attribute [local simp] Kourovka.Schreier.Transversal.rewrite_mk



set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X Q : Type*} [Group Q] (R : Set (FreeGroup X))
  (π : PresentedGroup R →* Q)
namespace Kourovka.MetabelianEnumeration.SchreierHeights
theorem _root_.solution (S : Transversal (preKernel R π))
    (z : S.Edge) :
    (schreierKernelEquiv R π S (PresentedGroup.of z)).val =
      PresentedGroup.mk R (S.edgeValue z) := by
  simp [schreierKernelEquiv, kernelQuotientEquiv, kernelMap,
    QuotientGroup.quotientKerEquivOfSurjective, QuotientGroup.quotientKerEquivOfRightInverse]
  rfl
end Kourovka.MetabelianEnumeration.SchreierHeights
