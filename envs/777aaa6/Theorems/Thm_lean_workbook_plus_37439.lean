-- Prove2me | Theorems.Thm_lean_workbook_plus_37439
-- name    : lean_workbook_plus_37439
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/ebd4c899-d4c7-4057-968a-a719be71ff67
-- statement:
--   Another solution $ab = 9$ $a+b = 12$ $(a+b)^2 = a^2 + 2ab + b^2$ $(a-b)^2 = a^2 - 2ab + b^2$ So, $(a-b)^2 = (a+b)^2 - 4ab = 144 - 4*9 = 108$ $|a-b| = \boxed{6\sqrt3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37439  (a b : ℝ)
  (h₀ : a * b = 9)
  (h₁ : a + b = 12) :
  |a - b| = 6 * Real.sqrt 3   :=  by sorry
