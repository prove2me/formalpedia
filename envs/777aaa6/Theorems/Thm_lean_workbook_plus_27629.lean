-- Prove2me | Theorems.Thm_lean_workbook_plus_27629
-- name    : lean_workbook_plus_27629
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/4df8a22e-b9cc-4c8f-a76d-78499bd1a3e5
-- statement:
--   Let $z=a+bi$ where $a$ and $b$ are real. This makes the expression: \n\n $$\sqrt{\frac{a^2+b^2+2a+1}{a^2+b^2+1}}+\sqrt{\frac{a^2+b^2-2a+1}{a^2+b^2+1}}$$ $$=\sqrt{1+\frac{2a}{a^2+b^2+1}}+\sqrt{1-\frac{2a}{a^2+b^2+1}}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27629  (a b : ℝ) :
  Real.sqrt ((a^2 + b^2 + 2 * a + 1) / (a^2 + b^2 + 1)) +
    Real.sqrt ((a^2 + b^2 - 2 * a + 1) / (a^2 + b^2 + 1)) =
    Real.sqrt (1 + (2 * a) / (a^2 + b^2 + 1)) +
    Real.sqrt (1 - (2 * a) / (a^2 + b^2 + 1))   :=  by sorry
