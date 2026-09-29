-- Prove2me | Theorems.Thm_lean_workbook_plus_9051
-- name    : lean_workbook_plus_9051
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/9cc63e7a-1104-46e7-bb22-d8cf767ff303
-- statement:
--   For $ a, b, c $ non-negative numbers prove that:\n\n $ (a^2+ab+b^2)(b^2+bc+c^2)(c^2+ca+a^2) \ge \n\n \frac{1}{3} \cdot (ab+bc+ca)^2 \cdot (a+b+c)^2 \ \ ; $\n\nGreetings!
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9051 (a b c : ℝ) : (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) ≥ 1 / 3 * (a * b + b * c + c * a)^2 * (a + b + c)^2   :=  by sorry
