-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_shift_mem
-- name    : Kourovka.MetabelianEnumeration.HalfspaceModule.shift_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:56.651429+00:00
-- url     : https://prove2.me/theorems/b09c4b24-4f77-4744-8e8a-10b13a5536ad
-- title:
--   Halfspace Module: shift mem
-- statement:
--   The Halfspace Module construction uses the shift mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceModule.lean#L51-L53
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceModule.lean#L51-L53

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Halfspaces_HalfspaceModule
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceModule
open ValuationModule
variable {Q M : Type} [AddCommGroup Q] [DecidableEq Q]
variable [AddCommGroup M] [Module (GroupRing Q) M]

theorem Kourovka.MetabelianEnumeration.HalfspaceModule.shift_mem (χ : Q →+ ℝ) (V : Submodule (nonnegativeRing χ) M)
    (q : Q) (hq : 0 ≤ χ q) (m : M) (hm : m ∈ V) : shift q m ∈ V := by sorry
