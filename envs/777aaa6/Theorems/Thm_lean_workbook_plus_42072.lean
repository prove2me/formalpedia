-- Prove2me | Theorems.Thm_lean_workbook_plus_42072
-- name    : lean_workbook_plus_42072
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/bac3a4b8-ddab-4fc3-8cd4-c662edde30d9
-- statement:
--   Prove that for \(x, y, z \geq 0\) and \(x + y + z = 1\), \(\frac{1}{x^2 + 1} \leq \frac{54 - 27x}{50}\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42072 (x y z : ℝ) (hx : x + y + z = 1) (hx' : 0 ≤ x) (hy' : 0 ≤ y) (hz' : 0 ≤ z) : 1 / (x ^ 2 + 1) ≤ (54 - 27 * x) / 50   :=  by sorry
