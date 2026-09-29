-- Prove2me | Theorems.Thm_lean_workbook_plus_54546
-- name    : lean_workbook_plus_54546
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/89e92fe4-6a7b-4f7a-b0b1-861b1401f24c
-- statement:
--   Let $a$ , $b$ , $c$ be the lengts of the sides of a triangle. Prove that ${3\over 2}a^2\geq ab+ac-bc$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54546 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 3 / 2 * a ^ 2 ≥ a * b + a * c - b * c   :=  by sorry
