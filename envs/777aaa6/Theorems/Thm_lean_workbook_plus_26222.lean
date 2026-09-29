-- Prove2me | Theorems.Thm_lean_workbook_plus_26222
-- name    : lean_workbook_plus_26222
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/51e5e4a0-db96-48a1-b6c9-2b54ba09a61a
-- statement:
--   Prove that $(a+b) ^2 + (b+c) ^2 + (c+a) ^2 \ge \frac{(2(a+b+c)) ^2}{3} = \frac{4(a+b+c) ^2}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26222 (a b c : ℝ) : (a + b) ^ 2 + (b + c) ^ 2 + (c + a) ^ 2 ≥ (2 * (a + b + c)) ^ 2 / 3   :=  by sorry
