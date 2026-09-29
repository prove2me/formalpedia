-- Prove2me | Theorems.Thm_lean_workbook_plus_8000
-- name    : lean_workbook_plus_8000
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3c02257c-de1b-4f85-9d48-d8c8cb7cc0a9
-- statement:
--   Prove that \(\cos2\alpha=2\cos^2\alpha-1\) for any \(\alpha\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8000 (α : ℝ) : Real.cos (2 * α) = 2 * (Real.cos α)^2 - 1   :=  by sorry
