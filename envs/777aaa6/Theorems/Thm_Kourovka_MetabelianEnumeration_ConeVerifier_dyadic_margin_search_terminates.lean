-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_dyadic_margin_search_terminates
-- name    : Kourovka.MetabelianEnumeration.ConeVerifier.dyadic_margin_search_terminates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:55.308172+00:00
-- url     : https://prove2.me/theorems/79cc18d0-091c-4013-bf5d-1a87612cf54e
-- title:
--   Cone Verifier: dyadic margin search terminates
-- statement:
--   There is an accepted dyadic margin, so sequential search through these
--   finite computations terminates for every cone cover.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeMargin.lean#L93-L104
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeMargin.lean#L93-L104

import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_Kourovka_Polyhedral_ConeMargin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier

theorem Kourovka.MetabelianEnumeration.ConeVerifier.dyadic_margin_search_terminates {n : ℕ} (supports : Supports n)
    (hc : ConeCover supports) : ∃ r : ℕ, checkMargin supports ((1 / 2 : ℚ) ^ r) = true := by sorry
