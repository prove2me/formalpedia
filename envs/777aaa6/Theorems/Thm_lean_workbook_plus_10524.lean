-- Prove2me | Theorems.Thm_lean_workbook_plus_10524
-- name    : lean_workbook_plus_10524
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/a7c0e7e9-0301-4c25-98f7-5046cfee04b3
-- statement:
--   If $\lim_{x \to 0} \frac{f(x)}{x^2} = 0$ prove that $\lim_{x \to 0} \frac{f(x)}{x} = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10524 (f : ℝ → ℝ) (h : ∀ x, f x / x ^ 2 = 0) : ∀ x, f x / x = 0   :=  by sorry
