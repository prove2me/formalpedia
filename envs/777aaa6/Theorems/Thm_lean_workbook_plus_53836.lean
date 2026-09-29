-- Prove2me | Theorems.Thm_lean_workbook_plus_53836
-- name    : lean_workbook_plus_53836
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/5f7b1c69-7fc6-4f5c-892c-883b0f2b5a0d
-- statement:
--   Prove the inequality $\frac{(a+b+c)^2}{3} \geq ab+bc+ca$ for positive numbers $a, b, c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53836 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a + b + c) ^ 2 / 3 ≥ a * b + b * c + c * a   :=  by sorry
