-- Prove2me | solution 1 for AttentionBudget.gate_le_retained_kstar
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-21T08:05:05.302361+00:00
-- url     : https://prove2.me/submissions/90eb7fd1-a4ea-403b-8655-7d921f254588

import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee

set_option autoImplicit false
open AttentionBudget

theorem solution : ¬ (∀ {w₀ : ℕ → ℝ}, (∀ i, 0 < w₀ i) →
    ∀ {w : ℕ → ℝ} {τ : ℝ} {n : ℕ},
      0 < n → τ ≤ 1 → τ ≤ retained w n (kstar w n τ)) := by
  intro h
  have hc := @h (fun _ => 1) (by intro i; norm_num)
    (fun _ => 0) 1 1 (by norm_num) (by norm_num)
  norm_num [retained, headMass] at hc
