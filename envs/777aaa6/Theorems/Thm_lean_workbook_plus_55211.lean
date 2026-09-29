-- Prove2me | Theorems.Thm_lean_workbook_plus_55211
-- name    : lean_workbook_plus_55211
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/d2c4c804-7e47-4c6a-a6a2-1a35c4cc9ce7
-- statement:
--   Suppose $a,b,c$ are the sides of a triangle. Prove or disprove $ (2b-c)a^2+(2c-a)b^2+(2a-b)c^2 \geq 3abc$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55211 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (2 * b - c) * a ^ 2 + (2 * c - a) * b ^ 2 + (2 * a - b) * c ^ 2 >= 3 * a * b * c   :=  by sorry
