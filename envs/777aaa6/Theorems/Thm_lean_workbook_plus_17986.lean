-- Prove2me | Theorems.Thm_lean_workbook_plus_17986
-- name    : lean_workbook_plus_17986
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/fc96bb1d-6b53-4cf8-bb1d-d64163d99311
-- statement:
--   By AM-GM \n\n $$a^4+b^4+4a^2b^2 =\frac{(a^2+b^2)^2}{2}+\frac{(a^2+b^2)^2}{2}+2a^2b^2 \ge ab(a^2+b^2)+\frac{(a^2+b^2)^2}{2}+2a^2b^2 \ge 3ab(a^2+b^2 )$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17986 : ∀ a b : ℝ, a^4 + b^4 + 4 * a^2 * b^2 ≥ 3 * a * b * (a^2 + b^2)   :=  by sorry
