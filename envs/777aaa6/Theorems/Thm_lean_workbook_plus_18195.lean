-- Prove2me | Theorems.Thm_lean_workbook_plus_18195
-- name    : lean_workbook_plus_18195
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/f7db2f69-028f-4d97-b050-0897995d7027
-- statement:
--   With the inequality $\frac{x(3-x)}{7-x} \le \frac{2}{9}x+\frac{1}{9}$ being true for $x\in [0,3]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18195 (x : ℝ) (hx: 0 ≤ x ∧ x ≤ 3) :
  x * (3 - x) / (7 - x) ≤ 2 / 9 * x + 1 / 9   :=  by sorry
