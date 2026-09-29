-- Prove2me | solution 1 for AttentionBudget.headMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T19:43:31.926477+00:00
-- url     : https://prove2.me/submissions/27f9a139-d20c-4fb5-a912-a7ced64222c0

import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee

open AttentionBudget
open Finset

variable {w : ℕ → ℝ} (hw : ∀ i, 0 < w i)
include hw

open AttentionBudget in
theorem solution {n : ℕ} (hn : 0 < n) : 0 < headMass w n :=
  Finset.sum_pos (fun i _ => hw i) ⟨0, mem_range.mpr hn⟩
