-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableLatticeBall_mem_interval
-- name    : Kourovka.MetabelianEnumeration.ComputableLatticeBall.mem_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:04.090857+00:00
-- url     : https://prove2.me/theorems/518205eb-d776-4538-97e7-d6c70d709328
-- title:
--   Computable Lattice Ball: mem interval
-- statement:
--   The Computable Lattice Ball construction uses the mem interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableLatticeBall.lean#L20-L28
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableLatticeBall.lean#L20-L28

import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableLatticeBall
open ComputableIntegers ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableLatticeBall.mem_interval (R : ℕ) (z : ℤ) : z ∈ interval R ↔ |z| ≤ (R : ℤ) := by sorry
