-- Prove2me | Theorems.Thm_lean_workbook_plus_1379
-- name    : lean_workbook_plus_1379
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/82147bf7-e45b-45a5-b94c-7ebc9bccc5db
-- statement:
--   If $a,b$ and $c$ are the sides of a triangle, prove that: $a^2(b + c - a) + b^2(c + a - b) + c^2(a + b - c)\leq 3abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1379 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ 3 * a * b * c   :=  by sorry
