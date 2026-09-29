-- Prove2me | Theorems.Thm_lean_workbook_plus_19668
-- name    : lean_workbook_plus_19668
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/445b5f01-4bc3-4eae-96c4-4790a6ff0cd8
-- statement:
--   $\cos{x}-\cos{y}=-2\sin{\frac{x+y}{2}}\sin{\frac{x-y}{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19668 : ∀ x y : ℝ, Real.cos x - Real.cos y = -2 * Real.sin ((x + y) / 2) * Real.sin ((x - y) / 2)   :=  by sorry
