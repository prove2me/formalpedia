-- Prove2me | Theorems.Thm_lean_workbook_plus_19205
-- name    : lean_workbook_plus_19205
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d7fcef6f-ffb7-4adf-8f5b-1560cbed91b3
-- statement:
--   Grace is thinking of two integers. Emmie observes that the sum of the two numbers is $56$ but the difference of the two numbers is $30$ . What is the sum of the squares of Grace's two numbers?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19205 (a b : ℤ) (h₁ : a + b = 56) (h₂ : a - b = 30) : a^2 + b^2 = 2018   :=  by sorry
