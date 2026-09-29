-- Prove2me | Theorems.Thm_lean_workbook_plus_17088
-- name    : lean_workbook_plus_17088
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/76c22145-a780-41c9-adf6-434ebe9545ae
-- statement:
--   Find $f(3)$ if $f(x) = ax^4 - bx^2 + x + 5$ and $f(-3) = 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17088 (a b : ℝ) (f : ℝ → ℝ) (h₁ : f = fun x => a * x ^ 4 - b * x ^ 2 + x + 5) (h₂ : f (-3) = 2) : f 3 = 8   :=  by sorry
