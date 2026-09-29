-- Prove2me | Theorems.Thm_lean_workbook_plus_29501
-- name    : lean_workbook_plus_29501
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/13370720-e34b-4145-8fe0-3501a528cc4f
-- statement:
--   Given the cubic equation $f(x)=x^3-20x^2+75x$, find $f(2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29501 (f : ℝ → ℝ) (f_def : ∀ x, f x = x^3 - 20 * x^2 + 75 * x) : f 2 = 78   :=  by sorry
