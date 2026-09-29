-- Prove2me | Theorems.Thm_lean_workbook_plus_57155
-- name    : lean_workbook_plus_57155
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/3891343d-3cf2-4e8f-a304-1a0974cf1ede
-- statement:
--   Suppose that $b_i < \frac1i$ for some $1 \le i \le 99.$ Let $c = \frac1i - b_i.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57155 (b : ℕ → ℚ) (hb : ∃ i, 1 ≤ i ∧ i ≤ 99 ∧ b i < 1 / i) : ∃ c, c = 1 / i - b i   :=  by sorry
