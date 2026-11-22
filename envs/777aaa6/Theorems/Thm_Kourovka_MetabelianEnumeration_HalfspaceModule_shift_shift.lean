-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceModule_shift_shift
-- name    : Kourovka.MetabelianEnumeration.HalfspaceModule.shift_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:47.300458+00:00
-- url     : https://prove2.me/theorems/e5f3f208-25b2-4ea3-9561-2213716c0f13
-- title:
--   Halfspace Module: shift shift
-- statement:
--   The Halfspace Module construction uses the shift shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceModule.lean#L41-L42
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceModule.lean#L41-L42

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Halfspaces_HalfspaceModule
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceModule
open ValuationModule
variable {Q M : Type} [AddCommGroup Q] [DecidableEq Q]
variable [AddCommGroup M] [Module (GroupRing Q) M]
omit [DecidableEq Q]

theorem Kourovka.MetabelianEnumeration.HalfspaceModule.shift_shift (q r : Q) (m : M) : shift q (shift r m) = shift (q + r) m := by sorry
