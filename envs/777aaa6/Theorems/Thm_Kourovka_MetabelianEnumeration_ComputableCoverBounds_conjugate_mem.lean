-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverBounds_conjugate_mem
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverBounds.conjugate_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:59:26.405003+00:00
-- url     : https://prove2.me/theorems/4dd8d9d7-1049-41fa-a896-67b83e014c70
-- title:
--   Computable Cover Bounds: conjugate mem
-- statement:
--   The Computable Cover Bounds construction uses the conjugate mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverBounds.lean#L40-L42
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverBounds.lean#L40-L42

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverBounds
open ComputableCoverData ComputableCoverWords

theorem Kourovka.MetabelianEnumeration.ComputableCoverBounds.conjugate_mem {n : ℕ} {x w : WordGroup} (hx : x ∈ bounded n)
    (hw : w ∈ bounded n) : FiniteCover.conjugate x w ∈ bounded n := by sorry
