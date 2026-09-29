-- Prove2me | Theorems.Thm_lean_workbook_plus_65111
-- name    : lean_workbook_plus_65111
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/85785b15-0407-47a4-80e4-81af4bb2a7c6
-- statement:
--   $f(x+u)-(x+u)^4=f(x)-x^4$ $\implies$ $f(x+u)-f(x)=4x^3u+6x^2u^2+4xu^3+u^4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65111 (f : ℝ → ℝ) (x u : ℝ) : f (x + u) - (x + u) ^ 4 = f x - x ^ 4 → f (x + u) - f x = 4 * x ^ 3 * u + 6 * x ^ 2 * u ^ 2 + 4 * x * u ^ 3 + u ^ 4   :=  by sorry
