-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.pathIn_length_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:19:43.583184+00:00
-- url     : https://prove2.me/submissions/f95c1aea-dec8-4f14-a50f-ba409379eedf

import Definitions.Def_Kourovka_Halfspaces_SchreierHeights
import Definitions.Def_Kourovka_Schreier_KernelPresentation
import Definitions.Def_Kourovka_Halfspaces_HalfspaceRelators
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_PathIn_mono
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
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X Q : Type*} [CommGroup Q]
namespace Kourovka.MetabelianEnumeration.SchreierHeights
theorem _root_.solution (f : X → ℝ) (D p : ℝ) (xs : List X)
    (hD0 : 0 ≤ D) (hD : ∀ x ∈ xs, |f x| ≤ D) :
    PathIn f (fun z => p - xs.length * D ≤ z ∧ z ≤ p + xs.length * D) p xs := by
  induction xs generalizing p with
  | nil => simp [PathIn]
  | cons x xs ih =>
    have hx := abs_le.mp (hD x List.mem_cons_self)
    have ht := ih (p + f x) (fun y hy => hD y (List.mem_cons_of_mem _ hy))
    constructor
    · have : (0 : ℝ) ≤ (x :: xs).length * D := mul_nonneg (Nat.cast_nonneg _) hD0
      exact ⟨by linarith, by linarith⟩
    · apply ht.mono
      intro z hz
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      constructor <;> nlinarith
end Kourovka.MetabelianEnumeration.SchreierHeights
