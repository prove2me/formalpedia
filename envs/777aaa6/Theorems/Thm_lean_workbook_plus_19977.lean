-- Prove2me | Theorems.Thm_lean_workbook_plus_19977
-- name    : lean_workbook_plus_19977
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/9151da49-4e8a-4c2a-b33a-3e120483218a
-- statement:
--   $\frac{1+abc}{a+b+c} \le \frac{\frac{3}{8}}{a+b+c} \le \frac{1}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19977 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 + a * b * c) / (a + b + c) ≤ (3 / 8) / (a + b + c) ∧ (3 / 8) / (a + b + c) ≤ 1 / 4   :=  by sorry
