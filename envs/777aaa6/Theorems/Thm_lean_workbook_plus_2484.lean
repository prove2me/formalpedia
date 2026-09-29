-- Prove2me | Theorems.Thm_lean_workbook_plus_2484
-- name    : lean_workbook_plus_2484
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/1848cb3f-980c-4a2e-a533-a986b3166758
-- statement:
--   The sum of three numbers is $96$ . The first number is $6$ times the third number, and the third number is $40$ less than the second number. What is the absolute value of the difference between the first and second numbers?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2484 (a b c : ℤ) (h₁ : a + b + c = 96) (h₂ : a = 6 * c) (h₃ : c = b - 40) : |a - b| = 5   :=  by sorry
