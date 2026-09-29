-- Prove2me | Theorems.Thm_lean_workbook_plus_31926
-- name    : lean_workbook_plus_31926
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/60f42831-b1f2-456c-927f-fed26b446a56
-- statement:
--   Prove that $\sum_\text{cyc} \frac{2ab-a^2 - b^2}{a^2 + b^2 + 2 c^2} = \sum_\text{cyc} \frac{-(a-b)^2}{a^2 + b^2 + 2 c^2} \le 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31926 (a b c : ℝ) :
  (2 * a * b - a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2 + 2 * c ^ 2) +
    (2 * b * c - b ^ 2 - c ^ 2) / (b ^ 2 + c ^ 2 + 2 * a ^ 2) +
      (2 * c * a - c ^ 2 - a ^ 2) / (c ^ 2 + a ^ 2 + 2 * b ^ 2) ≤
    0   :=  by sorry
