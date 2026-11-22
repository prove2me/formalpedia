-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.exists_safe_section
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:17:40.373469+00:00
-- url     : https://prove2.me/submissions/a19ac788-a3bb-4c04-89d4-c6c5fbb3e353

import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
import Definitions.Def_Kourovka_Schreier_PathLifting
import Definitions.Def_Kourovka_Halfspaces_SchreierHeights
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_value_mk
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_map_mk_of_perm
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_PathIn_toWord_mk
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_Within_pathIn
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_reorder_halfspaces
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
theorem _root_.solution [DecidableEq X] (π : FreeGroup X →* Q)
    (hπ : Function.Surjective π) (χ : Q →* Multiplicative ℝ)
    (D μ : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ x, |value (χ.comp π) (FreeGroup.of x)| ≤ D) (hμ : 2 * D ≤ μ) :
    ∃ r : Q → FreeGroup X, (∀ q, π (r q) = q) ∧ r 1 = 1 ∧
      ∀ q, PathIn (letterHeight fun x => value (χ.comp π) (FreeGroup.of x))
        (fun z => min 0 (χ q).toAdd ≤ z ∧ z ≤ max μ (χ q).toAdd) 0 (r q).toWord := by
  classical
  have hex : ∀ q : Q, ∃ w : FreeGroup X,
      π w = q ∧ (q = 1 → w = 1) ∧
      PathIn (letterHeight fun x => value (χ.comp π) (FreeGroup.of x))
        (fun z => min 0 (χ q).toAdd ≤ z ∧ z ≤ max μ (χ q).toAdd) 0 w.toWord := by
    intro q
    by_cases hq : q = 1
    · subst q
      refine ⟨1, map_one π, fun _ => rfl, ?_⟩
      simp [PathIn]
    obtain ⟨w, hw⟩ := hπ q
    obtain ⟨ys, hperm, hpath⟩ := reorder_halfspaces
      (letterHeight fun x => value (χ.comp π) (FreeGroup.of x)) D μ w.toWord
      (fun z _ => by rcases z with ⟨x, b⟩; cases b <;> simpa [letterHeight] using hD x)
      hD0 hμ
    have hsum : (w.toWord.map (letterHeight fun x => value (χ.comp π) (FreeGroup.of x))).sum =
        (χ q).toAdd := by
      rw [← value_mk, FreeGroup.mk_toWord]
      simp only [value, MonoidHom.comp_apply, hw]
    refine ⟨FreeGroup.mk ys, ?_, fun h => (hq h).elim, ?_⟩
    · rw [map_mk_of_perm π hperm, FreeGroup.mk_toWord, hw]
    · simpa only [hsum] using hpath.pathIn.toWord_mk
  choose r hr hnormal hpath using hex
  exact ⟨r, hr, hnormal 1 rfl, hpath⟩
end Kourovka.MetabelianEnumeration.SchreierHeights
