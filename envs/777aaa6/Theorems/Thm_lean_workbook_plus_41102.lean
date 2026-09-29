-- Prove2me | Theorems.Thm_lean_workbook_plus_41102
-- name    : lean_workbook_plus_41102
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/b57d1560-cfe3-4906-8e9f-823d00189f95
-- statement:
--   Show that $(f(x))^2 = x^4$ implies $f(x) = x^2$ or $f(x) = -x^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41102 (f : ℝ → ℝ) (hf: f x ^ 2 = x ^ 4) : f x = x ^ 2 ∨ f x = -x ^ 2   :=  by sorry
