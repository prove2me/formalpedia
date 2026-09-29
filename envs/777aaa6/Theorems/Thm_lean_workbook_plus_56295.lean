-- Prove2me | Theorems.Thm_lean_workbook_plus_56295
-- name    : lean_workbook_plus_56295
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/ea230331-0121-4ffe-8ec2-7166110a53b5
-- statement:
--   $ \frac {1}{bc} - \frac {1}{b(a + b)} - \frac {1}{c(a + c)} = \frac {2}{(a + b + c)^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56295 : ∀ a b c : ℝ, (1 / (b * c) - 1 / (b * (a + b)) - 1 / (c * (a + c)) = 2 / (a + b + c) ^ 2)   :=  by sorry
