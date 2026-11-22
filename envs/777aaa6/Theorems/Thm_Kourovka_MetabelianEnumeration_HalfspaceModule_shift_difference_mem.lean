-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_shift_difference_mem
-- name    : Kourovka.MetabelianEnumeration.HalfspaceModule.shift_difference_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:59:16.180719+00:00
-- url     : https://prove2.me/theorems/89401bcd-80e5-4e3b-8f3e-d02f29884b2e
-- title:
--   Halfspace Module: shift difference mem
-- statement:
--   The Halfspace Module construction uses the shift difference mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceModule.lean#L114-L125
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceModule.lean#L114-L125

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Halfspaces_HalfspaceModule
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceModule
open ValuationModule
variable {Q M : Type} [AddCommGroup Q] [DecidableEq Q]
variable [AddCommGroup M] [Module (GroupRing Q) M]

theorem Kourovka.MetabelianEnumeration.HalfspaceModule.shift_difference_mem (χ : Q →+ ℝ) (u : Q) (hu : 0 ≤ χ u)
    (V : Submodule (nonnegativeRing χ) M) (m : M)
    (hm : shift u m - m ∈ V) (n : ℕ) : shift (n • u) m - m ∈ V := by sorry
