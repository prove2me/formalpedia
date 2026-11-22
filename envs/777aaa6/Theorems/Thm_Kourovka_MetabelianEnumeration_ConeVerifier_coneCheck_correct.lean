-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_coneCheck_correct
-- name    : Kourovka.MetabelianEnumeration.ConeVerifier.coneCheck_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:02:18.719037+00:00
-- url     : https://prove2.me/theorems/7ccf8fe5-e623-4e0d-a8eb-15d6d33fffad
-- title:
--   Cone Verifier: cone Check correct
-- statement:
--   The exact universally quantified cone-cover condition is decided by rational arithmetic.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeVerifier.lean#L203-L205
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeVerifier.lean#L203-L205

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin

theorem Kourovka.MetabelianEnumeration.ConeVerifier.coneCheck_correct {n : ℕ} (supports : Supports n) :
    checkMargin supports 0 = true ↔ ConeCover supports := by sorry
