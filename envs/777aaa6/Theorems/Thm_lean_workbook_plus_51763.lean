-- Prove2me | Theorems.Thm_lean_workbook_plus_51763
-- name    : lean_workbook_plus_51763
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/9165e5ab-30d0-4e39-a18c-51740507d028
-- statement:
--   For two numbers $a$ , $b$ , their harmonic mean is $\frac{2}{\frac{1}{a}+\frac{1}{b}}=\frac{2ab}{a+b}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51763 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : 2 / (1 / a + 1 / b) = 2 * a * b / (a + b)   :=  by sorry
