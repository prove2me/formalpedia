-- Prove2me | Theorems.Thm_lean_workbook_plus_61733
-- name    : lean_workbook_plus_61733
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/9188be52-4214-4594-9fb6-eceacc31f470
-- statement:
--   Let $a=x^2+4x+8$ , then $\frac {1}{\sqrt{x^2+4x+13}+\sqrt{x^2+4x+8}}=\frac{1}{10}\iff \frac{1}{\sqrt a+\sqrt{a+5}}=\frac{1}{10}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61733 (x : ℝ) (a : ℝ) (ha : a = x^2 + 4*x + 8) : (1 / (Real.sqrt (x^2 + 4*x + 13) + Real.sqrt (x^2 + 4*x + 8))) = 1 / 10 ↔ (1 / (Real.sqrt a + Real.sqrt (a + 5))) = 1 / 10   :=  by sorry
