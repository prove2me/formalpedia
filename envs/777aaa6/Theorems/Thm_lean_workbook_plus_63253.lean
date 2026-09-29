-- Prove2me | Theorems.Thm_lean_workbook_plus_63253
-- name    : lean_workbook_plus_63253
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/43d3b78a-bc35-479d-a4ca-d7e43781836b
-- statement:
--   If you have something like $|a|=b$ , you have to solve and consider when $a=b$ and when $a=-b$ . This is what twinbrian did when he set $x^2+2x-4=4$ and $x^2+2x-4=-4$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63253  (x : ℝ)
  (h₀ : abs (x^2 + 2 * x - 4) = 4) :
  x^2 + 2 * x - 4 = 4 ∨ x^2 + 2 * x - 4 = -4   :=  by sorry
