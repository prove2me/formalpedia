-- Prove2me | Theorems.Thm_lean_workbook_plus_5103
-- name    : lean_workbook_plus_5103
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/cec2b41a-de02-4ad1-abd5-0fd9981820d4
-- statement:
--   Prove that $\frac{1}{x^2-4x+9} \le \frac{x+2}{18}$ if $0 \le x \le 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5103 : ∀ x : ℝ, 0 ≤ x ∧ x ≤ 1 → 1 / (x ^ 2 - 4 * x + 9) ≤ (x + 2) / 18   :=  by sorry
