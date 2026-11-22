-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_BieriStrebelNecessity_kernel_loop_transport
-- name    : Kourovka.MetabelianEnumeration.BieriStrebelNecessity.kernel_loop_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:23:41.914955+00:00
-- url     : https://prove2.me/theorems/f24d0cea-b743-4fa8-93e2-66e2a2f61564
-- title:
--   Bieri Strebel Necessity: kernel loop transport
-- statement:
--   The Bieri Strebel Necessity construction uses the kernel loop transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/BieriStrebelNecessity.lean#L65-L76
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/BieriStrebelNecessity.lean#L65-L76

import Definitions.Def_Kourovka_Halfspaces_HalfspaceShift
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
import Definitions.Def_Kourovka_Halfspaces_BieriStrebelNecessity
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.BieriStrebelNecessity
open HalfspaceGeometry HalfspaceLoops SchreierHeights ValuationModule
open CommutatorModule SignedTameness
variable {X E L : Type} [Group E] [AddCommGroup L]

theorem Kourovka.MetabelianEnumeration.BieriStrebelNecessity.kernel_loop_transport {G : Type} [Group G] (e : G ≃* E)
    (π : E →* Multiplicative L) (χ : L →+ ℝ) (g : X → G) (P : ℝ → Prop)
    (n : (π.comp e.toMonoidHom).ker) (hn : n ∈ loopSet (π.comp e.toMonoidHom) χ g P) :
    kernelEquiv e π n ∈ loopSet π χ (fun x => e (g x)) P := by sorry
