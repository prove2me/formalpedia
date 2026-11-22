-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.BieriStrebelNecessity.zero_halfspace_generation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:28:46.467179+00:00
-- url     : https://prove2.me/submissions/9eb504d5-12c5-4a3f-bc2c-4c34279e27cc

import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
import Definitions.Def_Kourovka_Halfspaces_BieriStrebelNecessity
import Theorems.Thm_Kourovka_MetabelianEnumeration_BieriStrebelNecessity_kernel_loop_transport
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_finite_presentation_zero_halfspace_generation
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_transfer_generation


set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.BieriStrebelNecessity
open HalfspaceGeometry HalfspaceLoops SchreierHeights ValuationModule
open CommutatorModule SignedTameness
variable {X E L : Type} [Group E] [AddCommGroup L]
namespace Kourovka.MetabelianEnumeration.BieriStrebelNecessity
theorem _root_.solution [DecidableEq X] [Fintype X]
    (R : Set (FreeGroup X)) (hR : R.Finite) (e : PresentedGroup R ≃* E)
    (π : E →* Multiplicative L) (hπ : Function.Surjective π)
    (χ : L →+ ℝ) (hχ : χ ≠ 0) [IsMulCommutative π.ker] :
    Subgroup.closure (loopSet π χ (fun x : X => e (PresentedGroup.of x)) (fun z => 0 ≤ z)) = ⊤ ∨
      Subgroup.closure (loopSet π χ (fun x : X => e (PresentedGroup.of x)) (fun z => z ≤ 0)) = ⊤ := by
  let π₀ := π.comp e.toMonoidHom
  let ek := kernelEquiv e π
  have hab : ∀ a b : π₀.ker, Commute a b := by
    intro a b
    apply (commute_map_iff ek.injective).mp
    exact mul_comm _ _
  have h := finite_presentation_zero_halfspace_generation R hR π₀
    (hπ.comp e.surjective) χ hχ hab
  have ht (P : ℝ → Prop) (hgen : Subgroup.closure (loopSet π₀ χ PresentedGroup.of P) = ⊤) :
      Subgroup.closure (loopSet π χ (fun x : X => e (PresentedGroup.of x)) P) = ⊤ :=
    transfer_generation ek _ _ hgen (kernel_loop_transport e π χ PresentedGroup.of P)
  exact h.imp (ht _) (ht _)
end Kourovka.MetabelianEnumeration.BieriStrebelNecessity
