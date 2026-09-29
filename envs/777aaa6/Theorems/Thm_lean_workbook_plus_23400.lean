-- Prove2me | Theorems.Thm_lean_workbook_plus_23400
-- name    : lean_workbook_plus_23400
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/a2650cdf-1b9b-4069-ae6b-1274ce63ee99
-- statement:
--   Let $a > b > c$. Prove that $(a-b+1)^2 \ge 4(c-b)$ and $(c-a+1)^2 \ge 4(b-a)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23400 (a b c : ℝ) (h1 : a > b ∧ b > c) : (a - b + 1) ^ 2 ≥ 4 * (c - b) ∧ (c - a + 1) ^ 2 ≥ 4 * (b - a)   :=  by sorry
