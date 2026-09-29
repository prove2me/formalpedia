-- Prove2me | Theorems.Thm_lean_workbook_plus_73506
-- name    : lean_workbook_plus_73506
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/1fc7c4c1-bed2-4502-96bc-3b60283df4a3
-- statement:
--   If $a, b, c>0$ , prove that \n $\frac{a+2b+3c}{4a+5b+6c}+\frac{2a+3b+c}{5a+6b+4c}+\frac{3a+b+2c}{6a+4b+5c}\leq\frac{6}{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73506 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 2 * b + 3 * c) / (4 * a + 5 * b + 6 * c) + (2 * a + 3 * b + c) / (5 * a + 6 * b + 4 * c) + (3 * a + b + 2 * c) / (6 * a + 4 * b + 5 * c) ≤ 6 / 5   :=  by sorry
