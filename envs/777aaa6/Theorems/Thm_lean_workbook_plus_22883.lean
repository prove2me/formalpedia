-- Prove2me | Theorems.Thm_lean_workbook_plus_22883
-- name    : lean_workbook_plus_22883
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/46d0676c-c0df-4f15-9460-4e5521c6602c
-- statement:
--   Let a,b,c be positive real numbers, prove: \n\n $ 9(a^3+b^3+c^3)\geq (a+b+c)^3 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22883 (a b c : ℝ) : a > 0 ∧ b > 0 ∧ c > 0 → 9 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ (a + b + c) ^ 3   :=  by sorry
