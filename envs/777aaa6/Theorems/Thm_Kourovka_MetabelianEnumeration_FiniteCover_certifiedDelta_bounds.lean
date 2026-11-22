-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_certifiedDelta_bounds
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.certifiedDelta_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:23.15061+00:00
-- url     : https://prove2.me/theorems/630843c8-f40a-4a83-8544-b41873d37a2c
-- title:
--   Finite Cover: certified Delta bounds
-- statement:
--   The Finite Cover construction uses the certified Delta bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CertifiedRadius.lean#L48-L55
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CertifiedRadius.lean#L48-L55

import Definitions.Def_Kourovka_Polyhedral_Radius
import Definitions.Def_Kourovka_Polyhedral_ConeMargin
import Definitions.Def_Kourovka_Covers_CertifiedRadius
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover

theorem Kourovka.MetabelianEnumeration.FiniteCover.certifiedDelta_bounds {k : ℕ} (hk : 1 ≤ k) {C : ℚ} (hC : 0 < C) :
    0 < certifiedDelta k C ∧ certifiedDelta k C ≤ C / 4 ∧
      certifiedDelta k C < 1 / (2 * (k : ℚ)) := by sorry
