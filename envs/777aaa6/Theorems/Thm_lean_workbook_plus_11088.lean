-- Prove2me | Theorems.Thm_lean_workbook_plus_11088
-- name    : lean_workbook_plus_11088
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/9e6c0f21-11a2-4f55-a73c-3868dfa496cd
-- statement:
--   Given $x \ge 0$ , prove that $\frac{(x^2 + 1)^6}{2^7}+\frac12 \ge x^5 - x^3 + x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11088 (x : ℝ) (hx : x ≥ 0) : (x^2 + 1)^6 / 2^7 + 1 / 2 ≥ x^5 - x^3 + x   :=  by sorry
