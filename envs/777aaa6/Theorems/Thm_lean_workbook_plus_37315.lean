-- Prove2me | Theorems.Thm_lean_workbook_plus_37315
-- name    : lean_workbook_plus_37315
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/56ffd3fc-668e-486a-8837-6353cd74635e
-- statement:
--   If $a,b,c$ the sides of a triangle, does the inequality $2a^3+2b^3+2c^3+a^2 c+b^2 a+c^2 b \ge 3a^2 b+3b^2 c+3c^2 a$ hold?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37315 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 2 * a ^ 3 + 2 * b ^ 3 + 2 * c ^ 3 + a ^ 2 * c + b ^ 2 * a + c ^ 2 * b >= 3 * a ^ 2 * b + 3 * b ^ 2 * c + 3 * c ^ 2 * a   :=  by sorry
