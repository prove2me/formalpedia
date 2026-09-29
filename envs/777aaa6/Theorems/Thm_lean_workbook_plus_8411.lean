-- Prove2me | Theorems.Thm_lean_workbook_plus_8411
-- name    : lean_workbook_plus_8411
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/e1e4b49f-ab89-4d43-91ae-16fbc835db45
-- statement:
--   $f(x) = ax + bx + x + 5$ , if $f(-4) = 3$ , what is $f(4)$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8411 (a b : ℝ) (f : ℝ → ℝ) (h₁ : f = fun x => a * x + b * x + x + 5) : f (-4) = 3 → f 4 = 7   :=  by sorry
