-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.representative_height
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:16:49.468206+00:00
-- url     : https://prove2.me/submissions/ec5319d3-32af-4942-b9b8-8861c67b710f

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
theorem _root_.solution (π : FreeGroup X →* Q) (χ : Q →* Multiplicative ℝ)
    (S : Transversal π.ker) (w : FreeGroup X) :
    value (χ.comp π) (S.rep w) = value (χ.comp π) w := by
  have h := S.sameCoset w
  have heq : π w = π (S.rep w) := by
    apply mul_inv_eq_one.mp
    simpa [MonoidHom.mem_ker] using h
  simp only [value, MonoidHom.comp_apply, heq]
end Kourovka.MetabelianEnumeration.SchreierHeights
