-- Prove2me | Theorems.Thm_lean_workbook_plus_9177
-- name    : lean_workbook_plus_9177
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/e9cd0cab-3510-4e88-987e-849314f84f88
-- statement:
--   Find $b$ given $a = 3$ and $b = a\sqrt{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9177 (a b : ℝ) (h₁ : a = 3) (h₂ : b = a * Real.sqrt 2) : b = 3 * Real.sqrt 2   :=  by sorry
