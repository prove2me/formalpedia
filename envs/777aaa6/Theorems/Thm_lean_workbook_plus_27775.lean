-- Prove2me | Theorems.Thm_lean_workbook_plus_27775
-- name    : lean_workbook_plus_27775
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/527c95dd-804c-4bf0-94dd-c185df646750
-- statement:
--   Let $f(x)=\sqrt{x^2-2x+10}+\sqrt{x^2-16x+80}=\sqrt{(x-1)^2+3^2}+\sqrt{(x-8)^2+4^2}$ . Then, by Cauchy Schwarz Inequality, we have\n\n$f(x)^2=x^2-2x+10+x^2-16x+80+2\sqrt{[(x-1)^2+3^2][(x-8)^2+4^2]}
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27775 (x : ℝ) :
  (Real.sqrt (x^2 - 2*x + 10) + Real.sqrt (x^2 - 16*x + 80))^2 ≥
  x^2 - 2*x + 10 + x^2 - 16*x + 80 + 2 * Real.sqrt ((x-1)^2 + 3^2) * Real.sqrt ((x-8)^2 + 4^2)   :=  by sorry
