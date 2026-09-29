-- Prove2me | Theorems.Thm_lean_workbook_plus_22982
-- name    : lean_workbook_plus_22982
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/417f5f5e-dae2-40e0-96ea-8c0c74e98a40
-- statement:
--   $xyz+\frac{1}{xyz}-2=0\Rightarrow (xyz)^2-2(xyz)+1=0\Rightarrow xyz=\pm 1\Rightarrow \boxed{B}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22982 (x y z : ℝ) (h : x * y * z + 1 / (x * y * z) - 2 = 0) : (x * y * z) ^ 2 - 2 * (x * y * z) + 1 = 0   :=  by sorry
