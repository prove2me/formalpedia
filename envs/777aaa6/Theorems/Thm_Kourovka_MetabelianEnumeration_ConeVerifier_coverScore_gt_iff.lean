-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_coverScore_gt_iff
-- name    : Kourovka.MetabelianEnumeration.ConeVerifier.coverScore_gt_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:53:34.56772+00:00
-- url     : https://prove2.me/theorems/92adee00-8e42-42e9-a3de-c51b38c860cb
-- title:
--   Cone Verifier: cover Score gt iff
-- statement:
--   The Cone Verifier construction uses the cover Score gt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeMargin.lean#L33-L40
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeMargin.lean#L33-L40

import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_Kourovka_Polyhedral_ConeMargin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier

theorem Kourovka.MetabelianEnumeration.ConeVerifier.coverScore_gt_iff {n : ℕ} (supports : Supports n) (x : Fin n → ℝ)
    (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon < 1) :
    epsilon < coverScore supports x ↔
      ∃ support ∈ supports, ∀ u ∈ support, epsilon < dot u x := by sorry
