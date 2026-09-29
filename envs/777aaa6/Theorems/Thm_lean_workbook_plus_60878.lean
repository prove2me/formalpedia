-- Prove2me | Theorems.Thm_lean_workbook_plus_60878
-- name    : lean_workbook_plus_60878
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/37d8dfaa-3e14-4e7b-add0-e46500a1e84d
-- statement:
--   If $x+y=4$ and $xy=-12$ , what is the value of $x^2+5xy+y^2$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60878 (x y : ℝ) (h₁ : x + y = 4) (h₂ : x * y = -12) : x^2 + 5 * (x * y) + y^2 = -20   :=  by sorry
