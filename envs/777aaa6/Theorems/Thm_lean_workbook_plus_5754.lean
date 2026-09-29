-- Prove2me | Theorems.Thm_lean_workbook_plus_5754
-- name    : lean_workbook_plus_5754
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/b422ecf4-31bc-40d1-a481-5e229a941640
-- statement:
--   Prove that $36+2\cdot\frac{p^3}{3} \ge 18p \iff (p-3)^2(p+6) \ge0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5754 (p : ℝ) : 36 + 2 * (p ^ 3 / 3) ≥ 18 * p ↔ (p - 3) ^ 2 * (p + 6) ≥ 0   :=  by sorry
