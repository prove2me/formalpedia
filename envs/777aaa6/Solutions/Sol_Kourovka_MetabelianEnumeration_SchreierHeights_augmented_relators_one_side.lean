-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.augmented_relators_one_side
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:20:52.127432+00:00
-- url     : https://prove2.me/submissions/78eb3123-08a5-425d-a42d-cc83c14b2d10

import Definitions.Def_Kourovka_Halfspaces_SchreierHeights
import Definitions.Def_Kourovka_Schreier_KernelPresentation
import Definitions.Def_Kourovka_Halfspaces_HalfspaceRelators
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_pathIn_length_bound
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_PathIn_mono
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_rewrite_mem_closure
import Theorems.Thm_Kourovka_Schreier_Transversal_edge_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_of
import Theorems.Thm_Kourovka_Schreier_Transversal_presentationEquiv_of
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_rewrite_eq_word
import Theorems.Thm_Kourovka_Schreier_Transversal_rewrite_mk
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
variable {X Q : Type*} [CommGroup Q]
namespace Kourovka.MetabelianEnumeration.SchreierHeights
theorem _root_.solution [DecidableEq X]
    (π : FreeGroup X →* Q) (χ : Q →* Multiplicative ℝ)
    (S : Transversal π.ker) (R : Set (FreeGroup X))
    (D B μ : ℝ) (hD0 : 0 ≤ D) (hDB : D ≤ B) (hμ : 2 * B ≤ μ)
    (hD : ∀ x, |value (χ.comp π) (FreeGroup.of x)| ≤ D)
    (hR : ∀ r ∈ R, (r.toWord.length : ℝ) * D ≤ B)
    (hsafe : ∀ t : S.vertices,
      PathIn (letterHeight fun x => value (χ.comp π) (FreeGroup.of x))
        (fun z => min 0 (value (χ.comp π) t.val) ≤ z ∧
          z ≤ max μ (value (χ.comp π) t.val)) 0 t.val.toWord)
    (r : FreeGroup (S.Edge))
    (hr : r ∈ S.relators R) :
    r ∈ Subgroup.closure (FreeGroup.of '' symbolsIn (χ.comp π) S (fun z => 0 ≤ z)) ∨
      r ∈ Subgroup.closure (FreeGroup.of '' symbolsIn (χ.comp π) S (fun z => z ≤ μ)) := by
  rcases hr with hr | hr
  · obtain ⟨t, w, hw, rfl⟩ := hr
    have hp := pathIn_length_bound
      (letterHeight fun x => value (χ.comp π) (FreeGroup.of x)) D
      (value (χ.comp π) t.val) w.toWord hD0 (by
        rintro ⟨x, b⟩ _
        cases b <;> simpa only [letterHeight, Bool.false_eq_true, if_false, if_true, abs_neg]
          using hD x)
    have hb := hR w hw
    by_cases hlo : B ≤ value (χ.comp π) t.val
    · left
      rw [S.rewrite_eq_word]
      apply rewrite_mem_closure
      apply hp.mono
      intro z hz
      linarith [hz.1]
    · right
      rw [S.rewrite_eq_word]
      apply rewrite_mem_closure
      apply hp.mono
      intro z hz
      linarith [hz.2]
  · obtain ⟨t, rfl⟩ := hr
    dsimp only
    have hp := hsafe t
    by_cases ht : 0 ≤ value (χ.comp π) t.val
    · left
      rw [S.rewrite_eq_word]
      apply rewrite_mem_closure
      rw [value_one]
      apply hp.mono
      intro z hz
      simpa only [min_eq_left ht] using hz.1
    · right
      rw [S.rewrite_eq_word]
      apply rewrite_mem_closure
      rw [value_one]
      apply hp.mono
      intro z hz
      have hμ0 : 0 ≤ μ := by linarith
      simpa only [max_eq_left (by linarith : value (χ.comp π) t.val ≤ μ)] using hz.2
end Kourovka.MetabelianEnumeration.SchreierHeights
