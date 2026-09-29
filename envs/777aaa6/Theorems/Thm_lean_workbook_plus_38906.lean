-- Prove2me | Theorems.Thm_lean_workbook_plus_38906
-- name    : lean_workbook_plus_38906
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/daab3838-4e5d-4882-8bc4-81ef84665f0d
-- statement:
--   Prove that $(t-\frac{1}{t})^2 \ge 0$ for $t > 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38906 (t : ℝ) (ht : t > 0) : (t - 1/t)^2 ≥ 0   :=  by sorry
