-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableLatticeBall_normSq_ofFn
-- name    : Kourovka.MetabelianEnumeration.ComputableLatticeBall.normSq_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:06.083247+00:00
-- url     : https://prove2.me/theorems/f00b2350-0408-40de-9d35-48413d7b989b
-- title:
--   Computable Lattice Ball: norm Sq of Fn
-- statement:
--   The Computable Lattice Ball construction uses the norm Sq of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableLatticeBall.lean#L66-L68
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableLatticeBall.lean#L66-L68

import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableLatticeBall
open ComputableIntegers ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableLatticeBall.normSq_ofFn {k : ℕ} (v : Fin k → ℤ) :
    (normSq (List.ofFn v) : ℤ) = ∑ i, v i ^ 2 := by sorry
