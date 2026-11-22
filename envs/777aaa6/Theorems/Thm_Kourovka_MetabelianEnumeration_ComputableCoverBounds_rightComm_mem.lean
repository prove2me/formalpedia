-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverBounds_rightComm_mem
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverBounds.rightComm_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:00:23.729367+00:00
-- url     : https://prove2.me/theorems/227494ea-6953-42b5-a32d-a43c1756671f
-- title:
--   Computable Cover Bounds: right Comm mem
-- statement:
--   The Computable Cover Bounds construction uses the right Comm mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverBounds.lean#L44-L47
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverBounds.lean#L44-L47

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverBounds
open ComputableCoverData ComputableCoverWords

theorem Kourovka.MetabelianEnumeration.ComputableCoverBounds.rightComm_mem {n : ℕ} {x y : WordGroup} (hx : x ∈ bounded n)
    (hy : y ∈ bounded n) : FiniteCover.rightComm x y ∈ bounded n := by sorry
