-- Prove2me | Theorems.Thm_lean_workbook_plus_17090
-- name    : lean_workbook_plus_17090
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/ad89b6be-5753-499e-aed7-ac3f87aa6633
-- statement:
--   Let a, b, c be three sides of a triangle. Prove that : $a^2 (b + c - a) + b^2 (c + a - b) + c^2 (a + b - c) \leq 3abc.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17090 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ 3 * a * b * c   :=  by sorry
