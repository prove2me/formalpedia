-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_le_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIntegers.le_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:59.803901+00:00
-- url     : https://prove2.me/theorems/67e7c599-f464-4c9f-8319-698e282aa71a
-- title:
--   Computable Integers: le primrec
-- statement:
--   The Computable Integers construction uses the le primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L77-L85
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L77-L85

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableIntegers.le_primrec : PrimrecRel (fun x y : ℤ => x ≤ y) := by sorry
