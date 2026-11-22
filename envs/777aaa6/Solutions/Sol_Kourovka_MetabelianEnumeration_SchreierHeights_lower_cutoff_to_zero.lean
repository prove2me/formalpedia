-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.lower_cutoff_to_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:25:50.139248+00:00
-- url     : https://prove2.me/submissions/4cde6344-d6c7-478f-a737-56ac6ab3648c

import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeneration
import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_exists_negative_path
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_PathIn_append
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_generatorWord_eval
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_path_inverse
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_path_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_schreierKernelEquiv_of
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_transfer_generation
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_value_mk
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
    (χ : L →+ ℝ) (hχ : χ ≠ 0) (μ : ℝ)
    (hgen : Subgroup.closure (loopSet π χ PresentedGroup.of (fun h => h ≤ μ)) = ⊤) :
    Subgroup.closure (loopSet π χ PresentedGroup.of (fun h => h ≤ 0)) = ⊤ := by
  let θ := χ.toMultiplicative.comp (π.comp (PresentedGroup.mk R))
  obtain ⟨s, hs, hshift⟩ := exists_negative_path R π hπ χ hχ μ
  change PathIn (step θ) (fun h => h ≤ 0) 0 s at hs
  let v := PresentedGroup.mk R (FreeGroup.mk s)
  let e : MulAut π.ker := MulAut.conjNormal v
  apply transfer_generation e _ _ hgen
  intro n hn
  obtain ⟨w, hw, hp⟩ := hn
  change PathIn (step θ) (fun h => h ≤ μ) 0 w at hp
  refine ⟨s ++ w ++ FreeGroup.invRev s, ?_, ?_⟩
  · rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, map_mul, map_mul, map_inv, hw]
    have heval : FreeGroup.lift (PresentedGroup.of : X → PresentedGroup R) (FreeGroup.mk s) = v :=
      (FreeGroup.lift_unique (PresentedGroup.mk R) (fun _ => rfl)).symm
    rw [heval]
    rfl
  · change PathIn (step θ) (fun h => h ≤ 0) 0 (s ++ w ++ FreeGroup.invRev s)
    have hwheight : value θ (FreeGroup.mk w) = 0 := by
      have hval : PresentedGroup.mk R (FreeGroup.mk w) = n.val := by
        rw [FreeGroup.lift_unique (PresentedGroup.mk R) (fun _ => rfl)]
        exact hw
      change χ (π (PresentedGroup.mk R (FreeGroup.mk w))).toAdd = 0
      rw [hval, n.property]
      exact χ.map_zero
    have hp' : PathIn (step θ) (fun h => h ≤ 0) (value θ (FreeGroup.mk s)) w := by
      have hh := path_shift θ (P := fun h => h ≤ μ) (Q := fun h => h ≤ 0)
        (value θ (FreeGroup.mk s)) hp (fun z hz => by
          change value θ (FreeGroup.mk s) + μ ≤ 0 at hshift
          linarith)
      simpa only [add_zero] using hh
    apply (hs.append (by simpa only [← value_mk, zero_add] using hp')).append
    have hi := path_inverse θ (fun h => h ≤ 0) 0 s hs
    simpa only [List.map_append, List.sum_append, ← value_mk, zero_add, hwheight, add_zero] using hi
end Kourovka.MetabelianEnumeration.SchreierHeights
