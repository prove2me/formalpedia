-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverBounds_polynomial_mem
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverBounds.polynomial_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:00:13.317652+00:00
-- url     : https://prove2.me/theorems/35e7f0fa-d90e-44dd-871e-4e5812fdc148
-- title:
--   Computable Cover Bounds: polynomial mem
-- statement:
--   The Computable Cover Bounds construction uses the polynomial mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverBounds.lean#L55-L63
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverBounds.lean#L55-L63

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverBounds
open ComputableCoverData ComputableCoverWords

theorem Kourovka.MetabelianEnumeration.ComputableCoverBounds.polynomial_mem {k n : ℕ} (hk : k ≤ n) {x : WordGroup}
    (hx : x ∈ bounded n) (p : PolynomialCode) : polynomial k x p ∈ bounded n := by sorry
