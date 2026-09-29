-- Prove2me | Theorems.Thm_lean_workbook_plus_23360
-- name    : lean_workbook_plus_23360
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/47b11761-a031-4d28-a390-4c6ad03b3274
-- statement:
--   Suppose a,b,c are sides of triangle. Prove that:\n $$a^2 (b + c - a) + b^2 (a+ c - b) + c^2 (a + b - c) \le\ 3 a b c$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23360 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^2 * (b + c - a) + b^2 * (a + c - b) + c^2 * (a + b - c) ≤ 3 * a * b * c   :=  by sorry
