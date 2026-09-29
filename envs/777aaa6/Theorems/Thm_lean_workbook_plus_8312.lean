-- Prove2me | Theorems.Thm_lean_workbook_plus_8312
-- name    : lean_workbook_plus_8312
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/a68193d5-4329-4f79-a10f-72b9fd0aae2d
-- statement:
--   Express $x, y, z$ in terms of $a, b, c$ using the equations $a = y+z, b = z+x, c = x+y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8312 (x y z a b c : ℝ) : a = y + z ∧ b = z + x ∧ c = x + y → x = (b + c - a) / 2 ∧ y = (a + c - b) / 2 ∧ z = (a + b - c) / 2   :=  by sorry
