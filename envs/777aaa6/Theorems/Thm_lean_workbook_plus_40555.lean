-- Prove2me | Theorems.Thm_lean_workbook_plus_40555
-- name    : lean_workbook_plus_40555
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/3c2dc1f5-4bf4-4baf-acc5-7e7c98f9d570
-- statement:
--   With the condition $a + b + c + 2 = abc$ and $a,b,c > 0$. Prove: $\frac{1}{a} + \frac{1}{b} + \frac{1}{c} \ge 4(a + b + c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40555 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c + 2 = a * b * c) : 1 / a + 1 / b + 1 / c ≥ 4 * (a + b + c)   :=  by sorry
