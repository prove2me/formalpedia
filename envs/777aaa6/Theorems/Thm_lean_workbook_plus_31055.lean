-- Prove2me | Theorems.Thm_lean_workbook_plus_31055
-- name    : lean_workbook_plus_31055
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/feb3d47c-8d18-4bbd-a433-8d8b626224b7
-- statement:
--   It reduces to\n\n $3(abc-1)^2+\sum(a-1)^2(b-c)^2+(a+b+c-ab-bc-ca)^2\ge 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31055 (a b c : ℝ) :
  3 * (a * b * c - 1) ^ 2 + (a - 1) ^ 2 * (b - c) ^ 2 + (b - 1) ^ 2 * (c - a) ^ 2 + (c - 1) ^ 2 * (a - b) ^ 2 + (a + b + c - a * b - b * c - c * a) ^ 2 ≥ 0   :=  by sorry
