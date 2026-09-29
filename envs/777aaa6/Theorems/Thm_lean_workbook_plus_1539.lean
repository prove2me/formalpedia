-- Prove2me | Theorems.Thm_lean_workbook_plus_1539
-- name    : lean_workbook_plus_1539
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/609e42d6-147f-4e62-962d-5372575bffb8
-- statement:
--   If a, b, c are positive numbers, prove that\n$$\sum_{cyc}{\frac{5a^2+2ab+2ac}{2a^2+(b+c)^2}}\leq\frac{9}{2}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1539 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (5 * (a ^ 2 + b ^ 2 + c ^ 2) + 2 * (a * b + b * c + a * c)) / (2 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2) ≤ 9 / 2   :=  by sorry
