-- Prove2me | Theorems.Thm_lean_workbook_plus_7629
-- name    : lean_workbook_plus_7629
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/afe2e7b7-9f2c-4d94-95c1-b0e584088447
-- statement:
--   For $ a, b, c, d > 0 $ real numbers prove that: $(a+b+c+d) \cdot (ab+ac+ad+bc+bd+cd) \ge 6 (abc+bcd+cda+dab) \ \ ; (1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7629 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + b + c + d) * (a * b + a * c + a * d + b * c + b * d + c * d) ≥ 6 * (a * b * c + b * c * d + c * d * a + d * a * b)   :=  by sorry
