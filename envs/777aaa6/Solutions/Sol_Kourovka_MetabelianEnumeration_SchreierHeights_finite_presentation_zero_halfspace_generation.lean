-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.finite_presentation_zero_halfspace_generation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:27:28.921125+00:00
-- url     : https://prove2.me/submissions/79bc1771-8e7f-4437-962d-e171cf407800

import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeneration
import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_lower_cutoff_to_zero
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_finite_presentation_halfspace_generation


set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry HalfspaceLoops
open Kourovka.Schreier.Transversal
variable {X L : Type} [AddCommGroup L] [DecidableEq X]
namespace Kourovka.MetabelianEnumeration.SchreierHeights
theorem _root_.solution [Fintype X]
    (R : Set (FreeGroup X)) (hRfinite : R.Finite)
    (π : PresentedGroup R →* Multiplicative L) (hπ : Function.Surjective π)
    (χ : L →+ ℝ) (hχ : χ ≠ 0) (habelian : ∀ a b : π.ker, Commute a b) :
    Subgroup.closure (loopSet π χ PresentedGroup.of (fun z => 0 ≤ z)) = ⊤ ∨
      Subgroup.closure (loopSet π χ PresentedGroup.of (fun z => z ≤ 0)) = ⊤ := by
  obtain ⟨μ, _, h | h⟩ := finite_presentation_halfspace_generation R hRfinite π hπ χ habelian
  · exact Or.inl h
  · exact Or.inr (lower_cutoff_to_zero R π hπ χ hχ μ h)
end Kourovka.MetabelianEnumeration.SchreierHeights
