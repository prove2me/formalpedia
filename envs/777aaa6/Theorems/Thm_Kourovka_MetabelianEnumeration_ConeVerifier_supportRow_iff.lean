-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_supportRow_iff
-- name    : Kourovka.MetabelianEnumeration.ConeVerifier.supportRow_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:50.325183+00:00
-- url     : https://prove2.me/theorems/0fce9d26-0b48-4c1f-9d35-74a9e5c60f8b
-- title:
--   Cone Verifier: support Row iff
-- statement:
--   The Cone Verifier construction uses the support Row iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeVerifier.lean#L26-L29
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeVerifier.lean#L26-L29

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin

theorem Kourovka.MetabelianEnumeration.ConeVerifier.supportRow_iff {n : ℕ} (u : Vec n) (epsilon : ℚ) (x : Fin n → ℝ) :
    (supportRow u epsilon).eval x ≤ 0 ↔ dot u x ≤ epsilon := by sorry
