-- Prove2me | Theorems.Thm_lean_workbook_plus_13564
-- name    : lean_workbook_plus_13564
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/b22a7a12-b374-4de0-a543-dfa561f08fdf
-- statement:
--   After some work (not too much) one gets the equivalent inequality \n $ \sum (b - c)^2(b + c)(b + c - a)(2a^2 + bc) \ge 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13564 {a b c : ℝ} (ha : a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (b - c) ^ 2 * (b + c) * (b + c - a) * (2 * a ^ 2 + b * c) + (c - a) ^ 2 * (c + a) * (c + a - b) * (2 * b ^ 2 + c * a) + (a - b) ^ 2 * (a + b) * (a + b - c) * (2 * c ^ 2 + a * b) ≥ 0   :=  by sorry
