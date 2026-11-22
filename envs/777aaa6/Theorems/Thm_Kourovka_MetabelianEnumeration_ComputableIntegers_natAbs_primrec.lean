-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_natAbs_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIntegers.natAbs_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:44:22.758882+00:00
-- url     : https://prove2.me/theorems/40e547aa-ef8a-49b9-849e-b56b3bfcb1bd
-- title:
--   Computable Integers: nat Abs primrec
-- statement:
--   The Computable Integers construction uses the nat Abs primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L36-L38
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L36-L38

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableIntegers.natAbs_primrec : Primrec Int.natAbs := by sorry
