-- Prove2me | Theorems.Thm_lean_workbook_plus_62013
-- name    : lean_workbook_plus_62013
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/e15f3675-c4a0-4932-b3ed-184089fded86
-- statement:
--   Adding the equations, we get\n\n $a^2 + b^2 + c^2 -ab - bc - ca = 18$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62013 (a b c : ℝ) (h1 : a + b + c = 18) (h2 : a^2 + b^2 + c^2 - a * b - b * c - c * a = 18) : a^2 + b^2 + c^2 - a * b - b * c - c * a = 18   :=  by sorry
