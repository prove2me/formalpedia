-- Prove2me | Theorems.Thm_lean_workbook_plus_66340
-- name    : lean_workbook_plus_66340
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/e0cbb711-7c6f-4f8a-b652-2bbd7e66adab
-- statement:
--   The sum of three numbers is $96$ . The first number is $6$ times the third number, and the third number is $40$ less than the second number. What is the absolute value of the difference between the first and second numbers?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66340 (x y z : ℤ) (h₁ : x + y + z = 96) (h₂ : x = 6 * z) (h₃ : z = y - 40) : |x - y| = 64   :=  by sorry
