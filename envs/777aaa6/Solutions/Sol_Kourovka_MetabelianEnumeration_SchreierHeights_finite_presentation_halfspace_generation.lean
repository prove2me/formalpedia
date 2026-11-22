-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.finite_presentation_halfspace_generation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:24:42.271661+00:00
-- url     : https://prove2.me/submissions/e90bcca2-038e-4c17-8d7f-955668b6c95f

import Definitions.Def_Kourovka_Halfspaces_SchreierPaths
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeneration
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_halfspace_generation_of_section
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_exists_safe_section
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
open HalfspaceGeometry HalfspaceSplitting HalfspaceLoops
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X L : Type} [AddCommGroup L] [DecidableEq X]
namespace Kourovka.MetabelianEnumeration.SchreierHeights
theorem _root_.solution [Fintype X]
    (R : Set (FreeGroup X)) (hRfinite : R.Finite)
    (π : PresentedGroup R →* Multiplicative L) (hπ : Function.Surjective π)
    (χ : L →+ ℝ) (habelian : ∀ a b : π.ker, Commute a b) :
    ∃ μ : ℝ, 0 ≤ μ ∧
      (Subgroup.closure (loopSet π χ PresentedGroup.of (fun z => 0 ≤ z)) = ⊤ ∨
        Subgroup.closure (loopSet π χ PresentedGroup.of (fun z => z ≤ μ)) = ⊤) := by
  classical
  let π₀ := π.comp (PresentedGroup.mk R)
  let θ := χ.toMultiplicative.comp π₀
  let D : ℝ := 1 + ∑ x : X, |value θ (FreeGroup.of x)|
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hD : ∀ x, |value θ (FreeGroup.of x)| ≤ D := by
    intro x
    have hh := Finset.single_le_sum (fun y _ => abs_nonneg (value θ (FreeGroup.of y)))
      (Finset.mem_univ x)
    dsimp [D]
    linarith
  let B := D + ∑ r ∈ hRfinite.toFinset, (r.toWord.length : ℝ) * D
  have hDB : D ≤ B := by
    dsimp [B]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun r _ => mul_nonneg (Nat.cast_nonneg _) hD0)
  have hR : ∀ r ∈ R, (r.toWord.length : ℝ) * D ≤ B := by
    intro r hr
    have hh := Finset.single_le_sum (fun w _ => mul_nonneg (Nat.cast_nonneg w.toWord.length) hD0)
      (hRfinite.mem_toFinset.mpr hr)
    dsimp [B]
    linarith
  let μ := 2 * B
  obtain ⟨r, hr, h1, hp⟩ := exists_safe_section π₀
    (hπ.comp (PresentedGroup.mk_surjective R)) χ.toMultiplicative D μ hD0 hD (by dsimp [μ]; linarith)
  let S := representativeOfSection π₀ r hr h1
  have hsafe : ∀ t : S.vertices,
      PathIn (step θ) (fun z => min 0 (value θ t.val) ≤ z ∧ z ≤ max μ (value θ t.val))
        0 t.val.toWord := by
    rintro ⟨_, ⟨w, rfl⟩⟩
    simpa only [S, representativeOfSection, step, θ, value, MonoidHom.comp_apply, hr] using hp (π₀ w)
  refine ⟨μ, by dsimp [μ]; linarith, ?_⟩
  exact halfspace_generation_of_section R π χ S D B μ hD0 hDB le_rfl hD hR hsafe habelian
end Kourovka.MetabelianEnumeration.SchreierHeights
