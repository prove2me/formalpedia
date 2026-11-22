-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.BieriStrebelNecessity.signed_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:29:52.689523+00:00
-- url     : https://prove2.me/submissions/29b89c7e-d614-472d-bc05-9360e8d60ac6

import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
import Definitions.Def_Kourovka_Halfspaces_BieriStrebelNecessity
import Theorems.Thm_Kourovka_MetabelianEnumeration_BieriStrebelNecessity_upper_loops_eq_negative_lower
import Theorems.Thm_Kourovka_MetabelianEnumeration_BieriStrebelNecessity_zero_halfspace_generation
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_finite_of_lower_loops_laurent


set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.BieriStrebelNecessity
open HalfspaceGeometry HalfspaceLoops SchreierHeights ValuationModule
open CommutatorModule SignedTameness
variable {X E L : Type} [Group E] [AddCommGroup L]
namespace Kourovka.MetabelianEnumeration.BieriStrebelNecessity
theorem _root_.solution [DecidableEq X] [Fintype X] [DecidableEq L]
    (R : Set (FreeGroup X)) (hR : R.Finite) (e : PresentedGroup R ≃* E)
    (π : E →* Multiplicative L) (hπ : Function.Surjective π)
    [IsMulCommutative π.ker] (χ : L →+ ℝ) (hχ : χ ≠ 0) :
    letI := laurentModule π hπ (MonoidHom.id (Multiplicative L))
    Module.Finite (GroupRing L) (Additive π.ker) →
    Module.Finite (nonnegativeRing χ) (Additive π.ker) ∨
      Module.Finite (nonnegativeRing (-χ)) (Additive π.ker) := by
  letI := laurentModule π hπ (MonoidHom.id (Multiplicative L))
  intro hf
  obtain h | h := zero_halfspace_generation R hR e π hπ χ hχ
  · right
    rw [upper_loops_eq_negative_lower] at h
    exact finite_of_lower_loops_laurent π (-χ) (neg_ne_zero.mpr hχ) hπ _ hf h
  · left
    exact finite_of_lower_loops_laurent π χ hχ hπ _ hf h
end Kourovka.MetabelianEnumeration.BieriStrebelNecessity
