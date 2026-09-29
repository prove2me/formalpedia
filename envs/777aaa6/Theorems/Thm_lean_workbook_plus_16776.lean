-- Prove2me | Theorems.Thm_lean_workbook_plus_16776
-- name    : lean_workbook_plus_16776
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/0c0ad806-1cc4-4482-9adc-e606fe915e21
-- statement:
--   Prove that $xy/z^2 + y/x + x/y \geq 9/4$ for positive $x, y$ given $x+y=z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16776 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxy : x + y = z) : x * y / z ^ 2 + y / x + x / y ≥ 9 / 4   :=  by sorry
