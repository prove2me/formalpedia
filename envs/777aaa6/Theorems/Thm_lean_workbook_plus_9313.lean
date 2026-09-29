-- Prove2me | Theorems.Thm_lean_workbook_plus_9313
-- name    : lean_workbook_plus_9313
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/5fadd8ee-5dec-466c-806a-d08f9797c899
-- statement:
--   i) $EC^2=a^2+b^2-2ab\cos{B+60}$\nii) $CF^2=a^2+b^2-2ab\cos(B+60)$\niii) $EF^2=a^2+b^2-2ab\cos(360-(180-B)-120)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9313 (a b : ℝ) (B : ℝ) : a^2 + b^2 - 2 * a * b * Real.cos (B + 60) = a^2 + b^2 - 2 * a * b * Real.cos (360 - (180 - B) - 120)   :=  by sorry
