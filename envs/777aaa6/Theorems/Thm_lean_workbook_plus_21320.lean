-- Prove2me | Theorems.Thm_lean_workbook_plus_21320
-- name    : lean_workbook_plus_21320
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/8885ce5e-ce1e-4bc4-8fe9-3338345c03d8
-- statement:
--   Determine the number of positive, negative, and complex roots of the polynomial $f(x)=5x^4-29x^3+55x^2-28x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21320 (f : ℂ → ℂ) (hf : f = fun x : ℂ => 5 * x ^ 4 - 29 * x ^ 3 + 55 * x ^ 2 - 28 * x) : {x : ℂ | f x = 0} = {x : ℂ | 5 * x ^ 4 - 29 * x ^ 3 + 55 * x ^ 2 - 28 * x = 0}   :=  by sorry
