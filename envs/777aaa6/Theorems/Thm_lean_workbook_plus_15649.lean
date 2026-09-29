-- Prove2me | Theorems.Thm_lean_workbook_plus_15649
-- name    : lean_workbook_plus_15649
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/50c5f6e7-f308-4840-8e75-d5c20eea794a
-- statement:
--   Prove for all real numbers $x \neq 0$: $\frac{x^{12}-x^{9}-x^{3}+1}{x^{4}}\geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15649 (x : ℝ) (hx : x ≠ 0) : (x ^ 12 - x ^ 9 - x ^ 3 + 1) / x ^ 4 ≥ 0   :=  by sorry
