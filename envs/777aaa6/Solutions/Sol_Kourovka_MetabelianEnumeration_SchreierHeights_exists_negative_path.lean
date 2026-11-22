-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.exists_negative_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:24:29.94168+00:00
-- url     : https://prove2.me/submissions/aceb2727-caad-49e6-8c3d-098a988b552c

import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeneration
import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_negative_letter_of_nonzero
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_path_replicate_nonpositive
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_value_mk


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
    (χ : L →+ ℝ) (hχ : χ ≠ 0) (μ : ℝ) :
    ∃ s : List (X × Bool),
      PathIn (letterHeight (fun x => χ (π (PresentedGroup.of x)).toAdd)) (fun h => h ≤ 0) 0 s ∧
      χ (π (PresentedGroup.mk R (FreeGroup.mk s))).toAdd + μ ≤ 0 := by
  let θ := χ.toMultiplicative.comp (π.comp (PresentedGroup.mk R))
  obtain ⟨z, hz⟩ := negative_letter_of_nonzero R π hπ χ hχ
  have hz' : 0 < -step θ z := by linarith
  obtain ⟨n, hn⟩ := exists_lt_nsmul hz' μ
  refine ⟨List.replicate n z, path_replicate_nonpositive θ z (le_of_lt hz) n, ?_⟩
  change value θ (FreeGroup.mk (List.replicate n z)) + μ ≤ 0
  rw [value_mk, List.map_replicate, List.sum_replicate]
  rw [nsmul_eq_mul] at hn ⊢
  nlinarith
end Kourovka.MetabelianEnumeration.SchreierHeights
