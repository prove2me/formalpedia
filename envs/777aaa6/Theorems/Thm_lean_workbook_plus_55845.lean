-- Prove2me | Theorems.Thm_lean_workbook_plus_55845
-- name    : lean_workbook_plus_55845
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/bd2c2eb7-143d-474e-b55a-922694ab6f95
-- statement:
--   Let $a,b,c>0$ and $a^2+b^2+c^2=1$ .Prove that $a+b+c+\frac{1}{15abc} \geq \frac{6\sqrt 3}{5}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55845 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : a + b + c + 1 / (15 * a * b * c) ≥ 6 * Real.sqrt 3 / 5   :=  by sorry
