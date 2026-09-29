-- Prove2me | Theorems.Thm_lean_workbook_plus_66333
-- name    : lean_workbook_plus_66333
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/b78f549b-e276-481c-ba2b-ac881571e35c
-- statement:
--   Evaluate $f(2) = 2^{\frac{1}{2}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66333 (f : ℝ → ℝ) (f_def : ∀ x, f x = x^(1/2)) : f 2 = 2^(1/2)   :=  by sorry
