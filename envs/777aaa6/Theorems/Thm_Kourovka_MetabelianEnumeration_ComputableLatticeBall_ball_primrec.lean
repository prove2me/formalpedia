-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableLatticeBall_ball_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableLatticeBall.ball_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:22.5097+00:00
-- url     : https://prove2.me/theorems/87ac1d52-1b5d-4ef6-9d01-d3e634e79c68
-- title:
--   Computable Lattice Ball: ball primrec
-- statement:
--   The Computable Lattice Ball construction uses the ball primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableLatticeBall.lean#L129-L133
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableLatticeBall.lean#L129-L133

import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableLatticeBall
open ComputableIntegers ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableLatticeBall.ball_primrec : Primrec₂ ball := by sorry
