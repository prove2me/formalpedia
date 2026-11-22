-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.coverScore_gt_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:32.102207+00:00
-- url     : https://prove2.me/submissions/9b9bf526-79d9-41bc-9738-8796e88f1a14

import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_Kourovka_Polyhedral_ConeMargin
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_supportScore_gt_iff

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (supports : Supports n) (x : Fin n → ℝ)
    (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon < 1) :
    epsilon < coverScore supports x ↔
      ∃ support ∈ supports, ∀ u ∈ support, epsilon < dot u x := by
  induction supports with
  | nil => simp [coverScore, not_lt.mpr he0]
  | cons support rest ih =>
    simp [coverScore, supportScore_gt_iff support x epsilon he1, ih]
end Kourovka.MetabelianEnumeration.ConeVerifier
