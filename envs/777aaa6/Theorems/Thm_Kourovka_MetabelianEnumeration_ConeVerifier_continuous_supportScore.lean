-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_continuous_supportScore
-- name    : Kourovka.MetabelianEnumeration.ConeVerifier.continuous_supportScore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:13.733806+00:00
-- url     : https://prove2.me/theorems/38214702-16a0-42d5-a288-1472d8247019
-- title:
--   Cone Verifier: continuous support Score
-- statement:
--   The Cone Verifier construction uses the continuous support Score property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeMargin.lean#L46-L50
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeMargin.lean#L46-L50

import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_Kourovka_Polyhedral_ConeMargin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier

theorem Kourovka.MetabelianEnumeration.ConeVerifier.continuous_supportScore {n : ℕ} (support : List (Vec n)) :
    Continuous (supportScore support) := by sorry
