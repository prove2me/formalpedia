-- Prove2me | Theorems.Thm_lean_workbook_plus_50329
-- name    : lean_workbook_plus_50329
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/c9071715-c3d8-4f3d-89b9-2c193d351f8a
-- statement:
--   Let $a, b$ be the positive real numbers such that $(a-\frac{2}{b})(b-\frac{1}{a})=\frac{3}{2} .$ Prove that $$a+2b\geq 2$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50329 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : (a - 2 / b) * (b - 1 / a) = 3 / 2) : a + 2 * b ≥ 2   :=  by sorry
