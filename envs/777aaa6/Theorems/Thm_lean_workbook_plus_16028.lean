-- Prove2me | Theorems.Thm_lean_workbook_plus_16028
-- name    : lean_workbook_plus_16028
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/58b745ef-6937-4d98-a0d4-fdfdeab72bae
-- statement:
--   Prove that $x^2+y^2+z^2 \ge \frac{1}{3}$ given $x+y+z=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16028 (x y z: ℝ) (h : x + y + z = 1) : x ^ 2 + y ^ 2 + z ^ 2 ≥ 1 / 3   :=  by sorry
