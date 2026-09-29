-- Prove2me | Theorems.Thm_lean_workbook_plus_75235
-- name    : lean_workbook_plus_75235
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/d58d021f-651e-48c3-8480-c88c41d97374
-- statement:
--   Show that $\frac{1}{(1-\theta)m+\theta M}\le \frac{1-\theta}{m}+\frac{\theta}{M}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75235 : ∀ m M : ℝ, ∀ θ : ℝ, (1 / ((1 - θ) * m + θ * M) ≤ (1 - θ) / m + θ / M)   :=  by sorry
