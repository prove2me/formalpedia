-- Prove2me | Theorems.Thm_lean_workbook_plus_17784
-- name    : lean_workbook_plus_17784
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d07fb2cb-fccc-4c62-8695-7b87ffb754a4
-- statement:
--   Determine if the function $y=\dfrac{\sin x}{1+x^4}$ is odd or even without graphing.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17784 (f : ℝ → ℝ) (f_def : ∀ x, f x = sin x / (1 + x ^ 4)) : ∀ x, f (-x) = -f x   :=  by sorry
