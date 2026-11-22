-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableLatticeBall_mem_ball
-- name    : Kourovka.MetabelianEnumeration.ComputableLatticeBall.mem_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:26.583182+00:00
-- url     : https://prove2.me/theorems/4803ceec-addd-4647-a354-91ae7a2fc16a
-- title:
--   Computable Lattice Ball: mem ball
-- statement:
--   The Computable Lattice Ball construction uses the mem ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableLatticeBall.lean#L73-L93
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableLatticeBall.lean#L73-L93

import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableLatticeBall
open ComputableIntegers ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableLatticeBall.mem_ball (k R : ℕ) (v : List ℤ) : v ∈ ball k R ↔
    ∃ w : Fin k → ℤ, List.ofFn w = v ∧ (∑ i, w i ^ 2) < (R : ℤ) ^ 2 := by sorry
