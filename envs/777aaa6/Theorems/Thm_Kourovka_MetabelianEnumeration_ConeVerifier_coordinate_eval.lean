-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_coordinate_eval
-- name    : Kourovka.MetabelianEnumeration.ConeVerifier.coordinate_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:47:14.453188+00:00
-- url     : https://prove2.me/theorems/5a6d412b-b1df-492f-bdef-6bde75f0f57b
-- title:
--   Cone Verifier: coordinate eval
-- statement:
--   The Cone Verifier construction uses the coordinate eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeVerifier.lean#L64-L66
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeVerifier.lean#L64-L66

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin

theorem Kourovka.MetabelianEnumeration.ConeVerifier.coordinate_eval {n : ℕ} (i : Fin n) (a b : ℚ) (x : Fin n → ℝ) :
    (coordinate i a b).eval x = (a : ℝ) * x i + b := by sorry
