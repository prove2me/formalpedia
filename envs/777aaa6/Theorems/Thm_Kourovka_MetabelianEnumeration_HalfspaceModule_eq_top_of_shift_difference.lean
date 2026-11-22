-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_eq_top_of_shift_difference
-- name    : Kourovka.MetabelianEnumeration.HalfspaceModule.eq_top_of_shift_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:59:20.443064+00:00
-- url     : https://prove2.me/theorems/b0fb6a5c-4bae-48a2-a3aa-e1e31073f2e5
-- title:
--   Halfspace Module: eq top of shift difference
-- statement:
--   The Halfspace Module construction uses the eq top of shift difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceModule.lean#L127-L136
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceModule.lean#L127-L136

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Halfspaces_HalfspaceModule
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceModule
open ValuationModule
variable {Q M : Type} [AddCommGroup Q] [DecidableEq Q]
variable [AddCommGroup M] [Module (GroupRing Q) M]

theorem Kourovka.MetabelianEnumeration.HalfspaceModule.eq_top_of_shift_difference (χ : Q →+ ℝ) (u : Q) (hu : 0 < χ u)
    (V : Submodule (nonnegativeRing χ) M)
    (hspan : Submodule.span (GroupRing Q) (V : Set M) = ⊤)
    (hdiff : ∀ m : M, shift u m - m ∈ V) : V = ⊤ := by sorry
