-- Prove2me | solution 1 for AttentionBudget.knee_bracket
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-21T08:03:04.256648+00:00
-- url     : https://prove2.me/submissions/dba4a253-45eb-4a62-9cb0-2a7d83b48311

import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee

set_option autoImplicit false
open AttentionBudget

theorem solution : ¬ (∀ {w₀ : ℕ → ℝ}, (∀ i, 0 < w₀ i) →
    ∀ {w : ℕ → ℝ} {τ : ℝ} {n : ℕ},
      0 < n → τ ≤ 1 → ∀ {a b : ℕ},
      retained w n a < τ → τ ≤ retained w n b →
      a < kstar w n τ ∧ kstar w n τ ≤ b) := by
  intro h
  let w : ℕ → ℝ := fun i => if i = 0 then -1 else 2
  have hfail : retained w 2 1 < 0 := by
    norm_num [retained, headMass, w, Finset.sum_range_succ]
  have hpass : (0 : ℝ) ≤ retained w 2 0 := by
    norm_num [retained, headMass]
  have hc := @h (fun _ => 1) (by intro i; norm_num)
    w 0 2 (by norm_num) (by norm_num) 1 0 hfail hpass
  omega
