-- Prove2me | Theorems.Thm_lean_workbook_plus_72962
-- name    : lean_workbook_plus_72962
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/7650e074-a395-4815-a1dc-bec707b6c1e9
-- statement:
--   Solve the equation: \n\n $$\frac{x+a+1}{x}=a-x\implies {{x}^{2}}-(a-1)x+a+1=0$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72962 {x a : ℝ} (h₁ : x ≠ 0) (h₂ : a = 7) : (x + a + 1) / x = a - x ↔ x^2 - (a - 1) * x + a + 1 = 0   :=  by sorry
