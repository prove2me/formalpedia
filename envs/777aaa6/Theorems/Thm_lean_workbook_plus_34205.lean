-- Prove2me | Theorems.Thm_lean_workbook_plus_34205
-- name    : lean_workbook_plus_34205
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/6a0f1c57-cd13-4e9b-a2d6-88be36a974e2
-- statement:
--   We have $3a^2+(b+c)^2 - 4ac = (a-b-c)^2+(a-b+c)(a+b-c)+(a+b-c)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34205  (a b c : ℝ) :
  3 * a ^ 2 + (b + c) ^ 2 - 4 * a * c =
    (a - b - c) ^ 2 + (a - b + c) * (a + b - c) + (a + b - c) ^ 2   :=  by sorry
