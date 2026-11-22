-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.negative_letter_of_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:22:35.556419+00:00
-- url     : https://prove2.me/submissions/79473bca-b078-47c4-84d8-fb6f4c90a181

import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeneration
import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_generatorWord_eval
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_schreierKernelEquiv_of
import Theorems.Thm_Kourovka_Schreier_Transversal_edge_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_of
import Theorems.Thm_Kourovka_Schreier_Transversal_presentationEquiv_of
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_rewrite_mk
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
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry HalfspaceLoops
open Kourovka.Schreier.Transversal
variable {X L : Type} [AddCommGroup L] [DecidableEq X]
omit [DecidableEq X]
namespace Kourovka.MetabelianEnumeration.SchreierHeights
theorem _root_.solution (R : Set (FreeGroup X))
    (π : PresentedGroup R →* Multiplicative L) (hπ : Function.Surjective π)
    (χ : L →+ ℝ) (hχ : χ ≠ 0) :
    ∃ z : X × Bool,
      step (χ.toMultiplicative.comp (π.comp (PresentedGroup.mk R))) z < 0 := by
  let θ := χ.toMultiplicative.comp (π.comp (PresentedGroup.mk R))
  have hn : ∃ x : X, value θ (FreeGroup.of x) ≠ 0 := by
    by_contra! hh
    have heq : θ = 1 := by
      apply FreeGroup.ext_hom
      intro x
      apply Multiplicative.toAdd.injective
      exact hh x
    apply hχ
    ext l
    obtain ⟨g, hg⟩ := hπ (Multiplicative.ofAdd l)
    obtain ⟨w, hw⟩ := PresentedGroup.mk_surjective R g
    have hz := congrArg (fun f : FreeGroup X →* Multiplicative ℝ => (f w).toAdd) heq
    simpa [θ, MonoidHom.comp_apply, hw, hg] using hz
  obtain ⟨x, hx⟩ := hn
  rcases lt_or_gt_of_ne hx with h | h
  · exact ⟨(x, true), h⟩
  · exact ⟨(x, false), by change -value θ (FreeGroup.of x) < 0; linarith⟩
end Kourovka.MetabelianEnumeration.SchreierHeights
