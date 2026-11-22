-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_supportScore_gt_iff
-- name    : Kourovka.MetabelianEnumeration.ConeVerifier.supportScore_gt_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:14.216426+00:00
-- url     : https://prove2.me/theorems/81a1d53e-0206-47a2-817d-c10753ae6b9e
-- title:
--   Cone Verifier: support Score gt iff
-- statement:
--   The Cone Verifier construction uses the support Score gt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeMargin.lean#L26-L31
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeMargin.lean#L26-L31

import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_Kourovka_Polyhedral_ConeMargin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier

theorem Kourovka.MetabelianEnumeration.ConeVerifier.supportScore_gt_iff {n : ℕ} (support : List (Vec n)) (x : Fin n → ℝ)
    (epsilon : ℝ) (he : epsilon < 1) :
    epsilon < supportScore support x ↔ ∀ u ∈ support, epsilon < dot u x := by sorry
