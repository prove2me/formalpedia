-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableLatticeBall_mem_cube
-- name    : Kourovka.MetabelianEnumeration.ComputableLatticeBall.mem_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:10.204882+00:00
-- url     : https://prove2.me/theorems/4e4eb013-371e-4ee5-b61e-4a9a1407d3aa
-- title:
--   Computable Lattice Ball: mem cube
-- statement:
--   The Computable Lattice Ball construction uses the mem cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableLatticeBall.lean#L34-L62
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableLatticeBall.lean#L34-L62

import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableLatticeBall
open ComputableIntegers ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableLatticeBall.mem_cube (R k : ℕ) (v : List ℤ) : v ∈ cube R k ↔
    ∃ w : Fin k → ℤ, List.ofFn w = v ∧ ∀ i, |w i| ≤ (R : ℤ) := by sorry
