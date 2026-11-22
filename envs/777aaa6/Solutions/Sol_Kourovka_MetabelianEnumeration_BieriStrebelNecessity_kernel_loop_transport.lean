-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.BieriStrebelNecessity.kernel_loop_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:23:45.716212+00:00
-- url     : https://prove2.me/submissions/a1437a25-a5bd-4d0b-80a7-03e587b7b705

import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
import Definitions.Def_Kourovka_Halfspaces_BieriStrebelNecessity
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_difference_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_evalWord_cons
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_evalWord_nil
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_inv
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_letter
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_generatorWord_eval
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_schreierKernelEquiv_of
import Theorems.Thm_Kourovka_Schreier_Transversal_edge_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_of
import Theorems.Thm_Kourovka_Schreier_Transversal_presentationEquiv_of
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_rewrite_mk
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.difference_one
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.evalWord_cons
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.evalWord_nil
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.height_inv
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.height_letter
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.height_mul
attribute [local simp] Kourovka.MetabelianEnumeration.HalfspaceLoops.height_one
attribute [local simp] Kourovka.MetabelianEnumeration.SchreierHeights.generatorWord_eval
attribute [local simp] Kourovka.MetabelianEnumeration.SchreierHeights.schreierKernelEquiv_of
attribute [local simp] Kourovka.Schreier.Transversal.edge_vertex
attribute [local simp] Kourovka.Schreier.Transversal.evaluate_of
attribute [local simp] Kourovka.Schreier.Transversal.presentationEquiv_of
attribute [local simp] Kourovka.Schreier.Transversal.rep_rep
attribute [local simp] Kourovka.Schreier.Transversal.rep_vertex
attribute [local simp] Kourovka.Schreier.Transversal.rewrite_mk



set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.BieriStrebelNecessity
open HalfspaceGeometry HalfspaceLoops SchreierHeights ValuationModule
open CommutatorModule SignedTameness
variable {X E L : Type} [Group E] [AddCommGroup L]
namespace Kourovka.MetabelianEnumeration.BieriStrebelNecessity
theorem _root_.solution {G : Type} [Group G] (e : G ≃* E)
    (π : E →* Multiplicative L) (χ : L →+ ℝ) (g : X → G) (P : ℝ → Prop)
    (n : (π.comp e.toMonoidHom).ker) (hn : n ∈ loopSet (π.comp e.toMonoidHom) χ g P) :
    kernelEquiv e π n ∈ loopSet π χ (fun x => e (g x)) P := by
  obtain ⟨w, hw, hp⟩ := hn
  refine ⟨w, ?_, hp⟩
  have hh : FreeGroup.lift (fun x => e (g x)) = e.toMonoidHom.comp (FreeGroup.lift g) := by
    apply FreeGroup.ext_hom
    intro x
    simp
  rw [hh, MonoidHom.comp_apply, hw]
  rfl
end Kourovka.MetabelianEnumeration.BieriStrebelNecessity
