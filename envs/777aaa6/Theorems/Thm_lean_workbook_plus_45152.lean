-- Prove2me | Theorems.Thm_lean_workbook_plus_45152
-- name    : lean_workbook_plus_45152
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/fe14b706-a64b-40b3-b355-ba941bd937a7
-- statement:
--   Given $f(x) = ax^3 + bx^2 + cx + d$ , such that $f(0) = 1$ , $f(1) = 2$ , $f(2) = 4$ , $f(3) = 8$ . Find the value of $f(4)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45152 (a b c d : ℝ) (h₁ : a * 0 ^ 3 + b * 0 ^ 2 + c * 0 + d = 1) (h₂ : a * 1 ^ 3 + b * 1 ^ 2 + c * 1 + d = 2) (h₃ : a * 2 ^ 3 + b * 2 ^ 2 + c * 2 + d = 4) (h₄ : a * 3 ^ 3 + b * 3 ^ 2 + c * 3 + d = 8) : a * 4 ^ 3 + b * 4 ^ 2 + c * 4 + d = 15   :=  by sorry
