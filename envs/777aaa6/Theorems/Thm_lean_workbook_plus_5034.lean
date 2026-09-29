-- Prove2me | Theorems.Thm_lean_workbook_plus_5034
-- name    : lean_workbook_plus_5034
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/d81815d6-0355-4a53-ae19-80ad00e96a75
-- statement:
--   Substituting $ a=\frac{3b}{5}$ into the first known equation, we can solve for $ b$ : \n \begin{align*}\frac{3b}{5}+b&=24\\ 3b+5b&=120\\ b&=15\end{align*}
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5034 (a b : ℝ) (h₁ : a + b = 24) (h₂ : a = 3 * b / 5) : b = 15   :=  by sorry
