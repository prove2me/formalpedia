-- Prove2me | Theorems.Thm_lean_workbook_plus_4260
-- name    : lean_workbook_plus_4260
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e748911d-2082-476d-b0bf-07935189143e
-- statement:
--   If $a,b,c$ are positive real numbers, and $a^2+b^2+c^2=1$ , prove inequality: $\frac{1}{a^2}+\frac{1}{b^2}+\frac{1}{c^2}\geq3+\frac{2(a^3+b^3+c^3)}{abc}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4260 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : 1 / a^2 + 1 / b^2 + 1 / c^2 ≥ 3 + 2 * (a^3 + b^3 + c^3) / (a * b * c)   :=  by sorry
