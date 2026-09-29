-- Prove2me | Theorems.Thm_lean_workbook_plus_27379
-- name    : lean_workbook_plus_27379
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/64cbd81e-7252-4eba-954b-f571fe218996
-- statement:
--   Let $ 1\leq a,b\leq 2$ be real numbers. Prove that \n\n $ 2(a + b)^2\leq 9ab$ \nBecause $ (2a-b)(2b-a)\geq0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27379 (a b : ℝ) (ha : 1 ≤ a ∧ a ≤ 2) (hb : 1 ≤ b ∧ b ≤ 2): 2 * (a + b) ^ 2 ≤ 9 * a * b   :=  by sorry
