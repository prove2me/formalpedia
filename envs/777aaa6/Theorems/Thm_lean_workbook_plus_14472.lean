-- Prove2me | Theorems.Thm_lean_workbook_plus_14472
-- name    : lean_workbook_plus_14472
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/9704a071-2579-48a8-9282-07d574e85a3f
-- statement:
--   Determine the minimum value of $f (x)$ where\nf (x) = (3 sin x - 4 cos x - 10)(3 sin x + 4 cos x - 10).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14472 (x : ℝ) : (3 * Real.sin x - 4 * Real.cos x - 10) * (3 * Real.sin x + 4 * Real.cos x - 10) ≥ -49   :=  by sorry
