-- Prove2me | Theorems.Thm_lean_workbook_plus_7590
-- name    : lean_workbook_plus_7590
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/fcc20059-18bb-4f6b-97ad-650ad010d073
-- statement:
--   And so $2f(x)-3x+a=2a-2x+f(x)$ and so $\boxed{f(x)=x+a}$ $\forall x$ , which indeed is a solution, whatever is $a\in\mathbb R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7590 (f : ℝ → ℝ) (a : ℝ) (hf: f x = a + x) : (2 * f x - 3 * x + a = 2 * a - 2 * x + f x)   :=  by sorry
