-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableLatticeBall_normSq_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableLatticeBall.normSq_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:19.815237+00:00
-- url     : https://prove2.me/theorems/f0aeaeb0-2cd9-4b79-b77b-15a63b700b09
-- title:
--   Computable Lattice Ball: norm Sq primrec
-- statement:
--   The Computable Lattice Ball construction uses the norm Sq primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableLatticeBall.lean#L125-L127
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableLatticeBall.lean#L125-L127

import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableLatticeBall
open ComputableIntegers ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableLatticeBall.normSq_primrec : Primrec normSq := by sorry
