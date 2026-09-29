-- Prove2me | Theorems.Thm_lean_workbook_plus_78343
-- name    : lean_workbook_plus_78343
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/711d1b81-b388-4d14-bb9b-8c7a51ccfc5c
-- statement:
--   Consider the function: $ f(x)=(1-x)\sin \frac{1}{1-x},0 \le x <1;f(1)=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78343 (x : ℝ) (f : ℝ → ℝ) (hf: f = fun (x:ℝ) => (1-x)*Real.sin (1/(1-x))) : (∀ x, 0 ≤ x ∧ x < 1 → f x = (1-x)*Real.sin (1/(1-x))) ∧ (f 1 = 0)   :=  by sorry
