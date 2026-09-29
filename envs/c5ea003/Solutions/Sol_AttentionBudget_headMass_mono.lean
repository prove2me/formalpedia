-- Prove2me | solution 1 for AttentionBudget.headMass_mono
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T19:52:18.852044+00:00
-- url     : https://prove2.me/submissions/1f7e8f81-1399-4904-8beb-633d51e4cab6

import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee

open AttentionBudget
open Finset

variable {w : ℕ → ℝ} (hw : ∀ i, 0 < w i)
include hw

open AttentionBudget in
theorem solution : Monotone (headMass w) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hab) fun i _ _ => (hw i).le
