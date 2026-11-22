-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverBounds_of_mem
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverBounds.of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:59:45.803842+00:00
-- url     : https://prove2.me/theorems/1062d11b-d8d4-4d83-b3a7-2f016de46651
-- title:
--   Computable Cover Bounds: of mem
-- statement:
--   The Computable Cover Bounds construction uses the of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverBounds.lean#L35-L38
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverBounds.lean#L35-L38

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverBounds
open ComputableCoverData ComputableCoverWords

theorem Kourovka.MetabelianEnumeration.ComputableCoverBounds.of_mem {n i : ℕ} (h : i < n) : FreeGroup.of i ∈ bounded n := by sorry
