-- Prove2me | Theorems.Thm_lean_workbook_plus_4399
-- name    : lean_workbook_plus_4399
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/30bdaa83-4b38-4a39-8ff5-04a09723b265
-- statement:
--   prove \( \cos 3a = 4\cdot \cos^{3}a - 3\cos a \)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4399 (a : ℝ) : Real.cos (3 * a) = 4 * (Real.cos a)^3 - 3 * Real.cos a   :=  by sorry
