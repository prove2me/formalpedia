-- Prove2me | Theorems.Thm_lean_workbook_plus_33551
-- name    : lean_workbook_plus_33551
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/c69bb06d-354f-4bda-bbf0-e458e3b506de
-- statement:
--   If $ x^2+y^2+z^2=xyz+4 $ , then there exists $ a,b,c > 0 $ such that $ x= a+ \frac{1}{a} ,y= b+ \frac{1}{b} ,z= c+ \frac{1}{c} $ with $ abc=1 $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33551 (x y z : ℝ) (hx: x > 0 ∧ y > 0 ∧ z > 0)(habc : x * y * z = 1) (h : x^2 + y^2 + z^2 = x * y * z + 4) :  ∃ a b c :ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1 ∧ x = a + 1 / a ∧ y = b + 1 / b ∧ z = c + 1 / c   :=  by sorry
