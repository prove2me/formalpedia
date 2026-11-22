-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.BieriStrebelNecessity.upper_loops_eq_negative_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:23:47.32418+00:00
-- url     : https://prove2.me/submissions/e8b35e1e-d2c7-43cd-927b-7ed1e211898c

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


section
noncomputable section
namespace Kourovka.MetabelianEnumeration.BieriStrebelNecessity
open HalfspaceGeometry HalfspaceLoops SchreierHeights ValuationModule
open CommutatorModule SignedTameness
variable {X E L : Type} [Group E] [AddCommGroup L]
private theorem path_neg {f : X → ℝ} {P : ℝ → Prop} {p : ℝ} {xs : List X}
    (h : PathIn f P p xs) : PathIn (fun x => -f x) (fun z => P (-z)) (-p) xs := by
  induction xs generalizing p with
  | nil => simpa [PathIn] using h
  | cons x xs ih =>
    constructor
    · simpa using h.1
    · simpa only [neg_add_rev, add_comm] using ih h.2
end Kourovka.MetabelianEnumeration.BieriStrebelNecessity
end
end

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.BieriStrebelNecessity
open HalfspaceGeometry HalfspaceLoops SchreierHeights ValuationModule
open CommutatorModule SignedTameness
variable {X E L : Type} [Group E] [AddCommGroup L]
namespace Kourovka.MetabelianEnumeration.BieriStrebelNecessity
theorem _root_.solution (π : E →* Multiplicative L)
    (χ : L →+ ℝ) (g : X → E) :
    loopSet π χ g (fun z => 0 ≤ z) = loopSet π (-χ) g (fun z => z ≤ 0) := by
  have hstep : letterHeight (fun x => (-χ) (π (g x)).toAdd) =
      fun z => -letterHeight (fun x => χ (π (g x)).toAdd) z := by
    funext z
    rcases z with ⟨x, b⟩
    cases b <;> simp [letterHeight]
  ext n
  constructor
  · rintro ⟨w, hw, hp⟩
    refine ⟨w, hw, ?_⟩
    rw [hstep]
    simpa only [neg_zero, neg_nonneg] using path_neg hp
  · rintro ⟨w, hw, hp⟩
    refine ⟨w, hw, ?_⟩
    rw [hstep] at hp
    simpa only [neg_neg, neg_zero, neg_nonpos] using path_neg hp
end Kourovka.MetabelianEnumeration.BieriStrebelNecessity
