-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_finite_of_shift_difference
-- name    : Kourovka.MetabelianEnumeration.HalfspaceModule.finite_of_shift_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:59:22.996286+00:00
-- url     : https://prove2.me/theorems/3b037755-d922-4ca5-b8cc-51aa38ec4e91
-- title:
--   Halfspace Module: finite of shift difference
-- statement:
--   A finite spanning family plus finitely many difference generators suffices
--   to generate over the nonnegative valuation ring.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceModule.lean#L140-L153
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceModule.lean#L140-L153

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Halfspaces_HalfspaceModule
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceModule
open ValuationModule
variable {Q M : Type} [AddCommGroup Q] [DecidableEq Q]
variable [AddCommGroup M] [Module (GroupRing Q) M]

theorem Kourovka.MetabelianEnumeration.HalfspaceModule.finite_of_shift_difference [DecidableEq M] (χ : Q →+ ℝ) (u : Q) (hu : 0 < χ u)
    (s d : Finset M) (hs : Submodule.span (GroupRing Q) (s : Set M) = ⊤)
    (hdiff : ∀ m : M, shift u m - m ∈
      Submodule.span (nonnegativeRing χ) ((s ∪ d : Finset M) : Set M)) :
    Module.Finite (nonnegativeRing χ) M := by sorry
