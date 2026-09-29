-- Prove2me | Theorems.Thm_lean_workbook_plus_65653
-- name    : lean_workbook_plus_65653
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/8efa611d-dcac-4dd5-b268-394200f99157
-- statement:
--   Let $a,b,c$ be positive and $a+b+c=3.$ Prove that $a+b+c\geq \frac{3}{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65653 (a b c: ℝ) (habc : a + b + c = 3) (ha : a > 0 ∧ b > 0 ∧ c > 0): a + b + c >= 3 / 2   :=  by sorry
