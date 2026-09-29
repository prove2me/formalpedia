-- Prove2me | Theorems.Thm_lean_workbook_plus_58335
-- name    : lean_workbook_plus_58335
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/bb9a5f98-3afe-45b9-a498-cb462aaf2f11
-- statement:
--   Rightarrow $\frac{1}{x^2+yz} \leq \frac{y+z}{4xyz}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58335 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 1 / (x ^ 2 + y * z) ≤ (y + z) / (4 * x * y * z)   :=  by sorry
