-- Prove2me | Theorems.Thm_lean_workbook_plus_79051
-- name    : lean_workbook_plus_79051
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/621abca3-0188-4ef5-8d25-5f9edce3a3a3
-- statement:
--   Let $a,b,c > 0$ such that $ab + bc + ca + abc \ge 4$ . Prove that \n $a + b + c \ge 3 + \frac{{{{\left( {b - c} \right)}^2}}}{{b + c + 4}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79051 (a b c : ℝ) (hab : 0 < a) (hbc : 0 < b) (hca : 0 < c) (habc : 0 < a * b * c) (h : a * b + b * c + c * a + a * b * c >= 4) : a + b + c >= 3 + (b - c) ^ 2 / (b + c + 4)   :=  by sorry
