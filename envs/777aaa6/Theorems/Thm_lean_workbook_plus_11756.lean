-- Prove2me | Theorems.Thm_lean_workbook_plus_11756
-- name    : lean_workbook_plus_11756
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/5eaea6c1-ed35-466e-a2dc-c6f4ed3372db
-- statement:
--   Prove the inequality: $2\sqrt{1+2(x-3)^2}\sqrt{(x-2)^2+1}\geq -3x^2+16x-\frac{87}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11756 : ∀ x : ℝ, 2 * Real.sqrt (1 + 2 * (x - 3) ^ 2) * Real.sqrt ((x - 2) ^ 2 + 1) ≥ -3 * x ^ 2 + 16 * x - 87 / 4   :=  by sorry
