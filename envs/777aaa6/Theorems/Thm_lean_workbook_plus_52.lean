-- Prove2me | Theorems.Thm_lean_workbook_plus_52
-- name    : lean_workbook_plus_52
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/8798f16e-9c7c-491b-95bb-6e4e35188d11
-- statement:
--   Derive $ \cos^{2}2x = \frac{1+\cos 4x}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52 : ∀ x : ℝ, Real.cos (2 * x) ^ 2 = (1 + Real.cos (4 * x)) / 2   :=  by sorry
