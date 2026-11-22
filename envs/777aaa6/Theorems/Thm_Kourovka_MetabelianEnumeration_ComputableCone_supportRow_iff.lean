-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_supportRow_iff
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.supportRow_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:52:52.862246+00:00
-- url     : https://prove2.me/theorems/587faa3b-c225-446c-b1db-b171d3d74096
-- title:
--   Computable Cone: support Row iff
-- statement:
--   The Computable Cone construction uses the support Row iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L58-L76
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L58-L76

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_supportRow_iff

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.supportRow_iff (n r : ℕ) (v : VectorCode) (x : Fin n → ℝ) :
    (decodeRow n (supportRow r v)).eval x ≤ 0 ↔
      ConeVerifier.dot (decodeVector n v) x ≤ (1 / 2 : ℝ) ^ r := by sorry
