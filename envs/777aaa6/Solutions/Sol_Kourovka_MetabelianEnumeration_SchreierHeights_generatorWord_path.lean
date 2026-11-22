-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.generatorWord_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:22:28.269324+00:00
-- url     : https://prove2.me/submissions/ea50b48c-b01c-4a50-8cc2-418f98856f89

import Definitions.Def_Kourovka_Halfspaces_SchreierKernel
import Definitions.Def_Kourovka_Halfspaces_SchreierPaths
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_path_inverse
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_generatorWord_eval
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_pathIn_append_iff
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_schreierKernelEquiv_of
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_value_mk
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


attribute [local simp] Kourovka.MetabelianEnumeration.SchreierHeights.generatorWord_eval

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X : Type*}
namespace Kourovka.MetabelianEnumeration.SchreierHeights
theorem _root_.solution [DecidableEq X] {L : Subgroup (FreeGroup X)}
    (θ : FreeGroup X →* Multiplicative ℝ) (S : Transversal L)
    (hheight : ∀ w, value θ (S.rep w) = value θ w)
    (P : ℝ → Prop) (z : S.Edge)
    (hz : z ∈ symbolsIn θ S P)
    (hfrom : PathIn (step θ) P 0 z.1.val.toWord)
    (hto : PathIn (step θ) P 0 (S.rep (z.1.val * FreeGroup.of z.2)).toWord) :
    PathIn (step θ) P 0 (generatorWord S z) := by
  unfold generatorWord
  rw [pathIn_append_iff, pathIn_append_iff]
  refine ⟨⟨hfrom, ?_⟩, ?_⟩
  · rw [← value_mk, FreeGroup.mk_toWord, zero_add]
    change P (value θ z.1.val) ∧ P (value θ z.1.val + value θ (FreeGroup.of z.2))
    simpa only [symbolsIn, Set.mem_setOf_eq, value_mul] using hz
  · have hp := path_inverse θ P 0 _ hto
    simpa only [List.map_append, List.sum_append, ← value_mk, FreeGroup.mk_toWord, hheight, zero_add, List.map_singleton,
      List.sum_singleton, step, letterHeight, if_true, value_mul] using hp
end Kourovka.MetabelianEnumeration.SchreierHeights
