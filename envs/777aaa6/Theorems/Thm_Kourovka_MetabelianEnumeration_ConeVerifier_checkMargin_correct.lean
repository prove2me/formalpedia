-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_checkMargin_correct
-- name    : Kourovka.MetabelianEnumeration.ConeVerifier.checkMargin_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:42:24.123188+00:00
-- url     : https://prove2.me/theorems/eee2c72e-283e-433a-89da-9458791b173a
-- title:
--   Cone Verifier: check Margin correct
-- statement:
--   The Cone Verifier construction uses the check Margin correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeVerifier.lean#L138-L151
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeVerifier.lean#L138-L151

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin

theorem Kourovka.MetabelianEnumeration.ConeVerifier.checkMargin_correct {n : ℕ} (supports : Supports n) (epsilon : ℚ) :
    checkMargin supports epsilon = true ↔ CubeMargin supports epsilon := by sorry
