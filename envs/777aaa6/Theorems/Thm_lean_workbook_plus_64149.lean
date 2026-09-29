-- Prove2me | Theorems.Thm_lean_workbook_plus_64149
-- name    : lean_workbook_plus_64149
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/86d44a07-4c65-4d4a-9997-ecd68425d66a
-- statement:
--   Suppose $a, b, c$ are the three sides of a triangle. Prove that $a^3+b^3+2(a+b)c^2 \ge c^3 + 2(a^2+b^2)c+abc$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64149 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^3 + b^3 + 2 * (a + b) * c^2 ≥ c^3 + 2 * (a^2 + b^2) * c + a * b * c   :=  by sorry
