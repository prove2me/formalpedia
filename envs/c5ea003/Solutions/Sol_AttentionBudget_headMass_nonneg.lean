-- Prove2me | solution 1 for AttentionBudget.headMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T19:56:07.529472+00:00
-- url     : https://prove2.me/submissions/bd09244a-e535-44fd-baad-ceb772ae592d

import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee

open AttentionBudget
open Finset

variable {w : ℕ → ℝ} (hw : ∀ i, 0 < w i)
include hw

open AttentionBudget in
theorem solution (n : ℕ) : 0 ≤ headMass w n :=
  Finset.sum_nonneg fun i _ => (hw i).le
