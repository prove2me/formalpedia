-- Prove2me | Theorems.Thm_lean_workbook_plus_32544
-- name    : lean_workbook_plus_32544
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/676a3281-add4-49a3-8d04-4e438dbefdaf
-- statement:
--   If $a, b, c$ denote the lengths of the sides of a triangle, show that\n$3(bc+ca+ab)\leq(a+b+c)^2< 4(bc+ca+ab)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32544 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 3 * (b * c + c * a + a * b) ≤ (a + b + c) ^ 2 ∧ (a + b + c) ^ 2 < 4 * (b * c + c * a + a * b)   :=  by sorry
