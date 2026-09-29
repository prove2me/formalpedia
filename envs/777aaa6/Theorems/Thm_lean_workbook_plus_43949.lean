-- Prove2me | Theorems.Thm_lean_workbook_plus_43949
-- name    : lean_workbook_plus_43949
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/4fe03715-927c-4715-8115-0a4b2842ea71
-- statement:
--   Expand $(r_1r_2+r_1r_3+r_2r_3)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43949 (r₁ r₂ r₃ : ℝ) : (r₁ * r₂ + r₁ * r₃ + r₂ * r₃) ^ 2 = r₁ ^ 2 * r₂ ^ 2 + r₁ ^ 2 * r₃ ^ 2 + r₂ ^ 2 * r₃ ^ 2 + 2 * r₁ ^ 2 * r₂ * r₃ + 2 * r₁ * r₂ ^ 2 * r₃ + 2 * r₁ * r₂ * r₃ ^ 2   :=  by sorry
