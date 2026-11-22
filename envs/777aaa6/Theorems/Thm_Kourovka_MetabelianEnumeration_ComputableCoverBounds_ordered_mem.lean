-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverBounds_ordered_mem
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverBounds.ordered_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:59:28.259183+00:00
-- url     : https://prove2.me/theorems/8ada7f8e-ffe1-45dd-8e33-4f44f89fbe7c
-- title:
--   Computable Cover Bounds: ordered mem
-- statement:
--   The Computable Cover Bounds construction uses the ordered mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverBounds.lean#L49-L53
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverBounds.lean#L49-L53

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverBounds
open ComputableCoverData ComputableCoverWords

theorem Kourovka.MetabelianEnumeration.ComputableCoverBounds.ordered_mem {k n : ℕ} (hk : k ≤ n) (v : List ℤ) : ordered k v ∈ bounded n := by sorry
