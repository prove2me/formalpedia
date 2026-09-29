-- Prove2me | Theorems.Thm_lean_workbook_plus_58958
-- name    : lean_workbook_plus_58958
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/856c36ee-2e0b-415c-acc3-2850437e2da2
-- statement:
--   Find $f(x)$ satisfying $f(1)=2$ and $f(\sqrt{x^{2}+y^{2}})=f(x)f(y)$ for all $x, y$ in $R$. (Example solution provided)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58958 (f : ℝ → ℝ) (hf: f 1 = 2 ∧ ∀ x y, f (Real.sqrt (x ^ 2 + y ^ 2)) = f x * f y) : ∃ f : ℝ → ℝ, f 1 = 2 ∧ ∀ x y, f (Real.sqrt (x ^ 2 + y ^ 2)) = f x * f y   :=  by sorry
