-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_faceRows_iff
-- name    : Kourovka.MetabelianEnumeration.ConeVerifier.faceRows_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:47:16.612306+00:00
-- url     : https://prove2.me/theorems/71b435f4-fdfc-4470-add9-538e59ad35b4
-- title:
--   Cone Verifier: face Rows iff
-- statement:
--   The Cone Verifier construction uses the face Rows iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeVerifier.lean#L91-L104
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeVerifier.lean#L91-L104

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin

theorem Kourovka.MetabelianEnumeration.ConeVerifier.faceRows_iff {n : ℕ} (i : Fin n) (sign : ℚ) (x : Fin n → ℝ) :
    Satisfies (faceRows i sign) x ↔ x i = sign ∧ ∀ j, -1 ≤ x j ∧ x j ≤ 1 := by sorry
