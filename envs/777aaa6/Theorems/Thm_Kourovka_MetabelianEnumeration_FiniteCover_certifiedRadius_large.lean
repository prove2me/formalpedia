-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_certifiedRadius_large
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.certifiedRadius_large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:07.234746+00:00
-- url     : https://prove2.me/theorems/6cf8a2d7-2ec9-48e8-a164-16b4de99865b
-- title:
--   Finite Cover: certified Radius large
-- statement:
--   The Finite Cover construction uses the certified Radius large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CertifiedRadius.lean#L19-L44
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CertifiedRadius.lean#L19-L44

import Definitions.Def_Kourovka_Polyhedral_Radius
import Definitions.Def_Kourovka_Polyhedral_ConeMargin
import Definitions.Def_Kourovka_Covers_CertifiedRadius
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover

theorem Kourovka.MetabelianEnumeration.FiniteCover.certifiedRadius_large {k : ℕ} (hk : 1 ≤ k) {C D : ℚ}
    (hC : 0 < C) (hD : 1 ≤ D) (hCD : C ≤ D) :
    2 * (k : ℚ) < certifiedRadius k C D ∧
    2 * (k : ℚ) * D < certifiedRadius k C D ∧
    C < certifiedRadius k C D ∧
    D ^ 2 < C * certifiedRadius k C D := by sorry
