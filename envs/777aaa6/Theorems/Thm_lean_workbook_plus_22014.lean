-- Prove2me | Theorems.Thm_lean_workbook_plus_22014
-- name    : lean_workbook_plus_22014
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/3fd9e649-83db-4f74-9123-7d1024462a02
-- statement:
--   Let $ a,b,c$ be positive real numbers. Prove that $ \frac a{b}+\frac b{c}+\frac c{a} \ge 3+\frac {(a-c)^2}{b^2+ab+bc+ca}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22014 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a ≥ 3 + (a - c) ^ 2 / (b ^ 2 + a * b + b * c + c * a)   :=  by sorry
