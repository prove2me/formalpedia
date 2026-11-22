-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.symbols_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:19:54.910271+00:00
-- url     : https://prove2.me/submissions/6760a74f-3f90-4c2b-bab7-00210c97573d

import Definitions.Def_Kourovka_Halfspaces_SchreierHeights
import Definitions.Def_Kourovka_Schreier_KernelPresentation
import Definitions.Def_Kourovka_Halfspaces_HalfspaceRelators

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X Q : Type*} [CommGroup Q]
namespace Kourovka.MetabelianEnumeration.SchreierHeights
theorem _root_.solution (π : FreeGroup X →* Q) (χ : Q →* Multiplicative ℝ)
    (S : Transversal π.ker) (D μ : ℝ)
    (hD : ∀ x, |value (χ.comp π) (FreeGroup.of x)| ≤ D) (hμ : D ≤ μ)
    (z : S.Edge) :
    z ∈ symbolsIn (χ.comp π) S (fun x => 0 ≤ x) ∨
      z ∈ symbolsIn (χ.comp π) S (fun x => x ≤ μ) := by
  change (0 ≤ value (χ.comp π) z.1.val ∧ 0 ≤ value (χ.comp π)
    (z.1.val * FreeGroup.of z.2)) ∨ _
  by_cases h : 0 ≤ value (χ.comp π) z.1.val ∧ 0 ≤ value (χ.comp π)
      (z.1.val * FreeGroup.of z.2)
  · exact Or.inl h
  · right
    change value (χ.comp π) z.1.val ≤ μ ∧ value (χ.comp π)
      (z.1.val * FreeGroup.of z.2) ≤ μ
    rw [value_mul] at h ⊢
    have hb := abs_le.mp (hD z.2)
    push_neg at h
    constructor <;> by_contra! hh <;> have := h (by linarith) <;> linarith
end Kourovka.MetabelianEnumeration.SchreierHeights
