-- Prove2me | Theorems.Thm_lean_workbook_plus_26762
-- name    : lean_workbook_plus_26762
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/c5775082-b009-46f6-a7bf-312e4f3011dc
-- statement:
--   prove the inequality \n\n $a^3+b^3+c^3 + 6\\left(a^2b+b^2c+c^2a\\right) \geq 3\\left(ab^2+bc^2+ca^2\\right) +12abc$ \n\nfor every three positive real numbers a, b, c.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26762 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 + 6 * (a^2 * b + b^2 * c + c^2 * a) ≥ 3 * (a * b^2 + b * c^2 + c * a^2) + 12 * a * b * c   :=  by sorry
