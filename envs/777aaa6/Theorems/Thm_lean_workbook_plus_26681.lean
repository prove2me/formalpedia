-- Prove2me | Theorems.Thm_lean_workbook_plus_26681
-- name    : lean_workbook_plus_26681
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/3b81c2d9-1e75-4194-a7c4-68f2740d8e6e
-- statement:
--   Prove that $4b^2c^2 - (b^2 + c^2 - a^2)^2 = (a - b + c)(a + b - c)(b+c-a)(b+c+a)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26681 (a b c : ℝ) : 4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 = (a - b + c) * (a + b - c) * (b + c - a) * (b + c + a)   :=  by sorry
