-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_choices_correct
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.choices_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:53:08.827561+00:00
-- url     : https://prove2.me/theorems/a242c3e0-09a8-479b-b009-cfd82e2146a3
-- title:
--   Computable Cone: choices correct
-- statement:
--   The Computable Cone construction uses the choices correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L106-L128
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L106-L128

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.choices_correct (n r : ℕ) (supports : SupportsCode) (x : Fin n → ℝ) :
    (∃ rows ∈ choices r supports, Satisfies n rows x) ↔
      ∀ support ∈ supports, ∃ u ∈ support,
        ConeVerifier.dot (decodeVector n u) x ≤ (1 / 2 : ℝ) ^ r := by sorry
