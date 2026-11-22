-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableLatticeBall_interval_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableLatticeBall.interval_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:20.075017+00:00
-- url     : https://prove2.me/theorems/a39fbd32-3936-4a7f-af4a-3208aca9c88f
-- title:
--   Computable Lattice Ball: interval primrec
-- statement:
--   The Computable Lattice Ball construction uses the interval primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableLatticeBall.lean#L105-L110
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableLatticeBall.lean#L105-L110

import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableLatticeBall
open ComputableIntegers ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableLatticeBall.interval_primrec : Primrec interval := by sorry
