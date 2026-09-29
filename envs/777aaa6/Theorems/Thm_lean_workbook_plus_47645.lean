-- Prove2me | Theorems.Thm_lean_workbook_plus_47645
-- name    : lean_workbook_plus_47645
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ace61795-8a5c-4d49-a9e8-dc7ec9d6944a
-- statement:
--   Prove $g(x)=x^3+x+\frac{1}{x}-x^2>\frac32$ for all $x>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47645 (x : ℝ) (hx : x > 0) : x^3 + x + 1/x - x^2 > 3/2   :=  by sorry
