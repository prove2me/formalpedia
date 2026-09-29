-- Prove2me | Theorems.Thm_lean_workbook_plus_48907
-- name    : lean_workbook_plus_48907
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/f643bae3-3f70-47ea-b784-ada01f55b898
-- statement:
--   The sum of two integers is $8$ . The sum of the squares of those two integers is $34$ . What is the product of the two integers?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48907 (x y : ℤ) (h₁ : x + y = 8) (h₂ : x^2 + y^2 = 34) : x*y = 15   :=  by sorry
