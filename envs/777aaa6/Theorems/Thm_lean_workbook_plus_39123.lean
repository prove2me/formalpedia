-- Prove2me | Theorems.Thm_lean_workbook_plus_39123
-- name    : lean_workbook_plus_39123
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/69e9bd0a-2155-4905-a6f2-899632e36165
-- statement:
--   Prove that $\frac{\frac{1}{a}+\frac{1}{b}}{2}\geq\frac{2}{a+b}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39123 {a b : ℝ} (ha : a > 0) (hb : b > 0) : (1 / a + 1 / b) / 2 ≥ 2 / (a + b)   :=  by sorry
