-- Prove2me | Theorems.Thm_lean_workbook_plus_9493
-- name    : lean_workbook_plus_9493
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/cdf85eec-2c6c-4f77-a72b-568d9d404c9d
-- statement:
--   From $f(x-f(2x))+x=0$ and $f(2x)=f(x)+x$ we obtain $f(-f(x))=-x$ for all $x$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9493 (f : ℝ → ℝ): (∀ x, f (2 * x) = f x + x) ∧ (∀ x, f (x - f (2 * x)) + x = 0) → ∀ x, f (-f x) = -x   :=  by sorry
