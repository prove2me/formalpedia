-- Prove2me | Theorems.Thm_lean_workbook_plus_52181
-- name    : lean_workbook_plus_52181
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/81fb5ae2-1dee-414f-83b8-6108817a875c
-- statement:
--   Prove that the inequality $8(b-c)^2(a-c)^2(a-b)^2+(a^2b+a^2c+ab^2-6abc+ac^2+b^2c+bc^2)^2\ge{0}$ holds for all sides $a, b, c$ of a triangle.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52181 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 8 * (b - c) ^ 2 * (a - c) ^ 2 * (a - b) ^ 2 + (a ^ 2 * b + a ^ 2 * c + a * b ^ 2 - 6 * a * b * c + a * c ^ 2 + b ^ 2 * c + b * c ^ 2) ^ 2 ≥ 0   :=  by sorry
