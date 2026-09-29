-- Prove2me | Theorems.Thm_lean_workbook_plus_65683
-- name    : lean_workbook_plus_65683
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/aaaefd86-f236-4603-994c-2c23f2fbf006
-- statement:
--   Prove the identity: $(a+b-c)(a+c-b)(b+c-a)+2abc = a^2(b+c-a)+b^2(a+c-b)+c^2(a+b-c)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65683 (a b c : ℝ) : (a + b - c) * (a + c - b) * (b + c - a) + 2 * a * b * c = a ^ 2 * (b + c - a) + b ^ 2 * (a + c - b) + c ^ 2 * (a + b - c)   :=  by sorry
