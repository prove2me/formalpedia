-- Prove2me | Theorems.Thm_lean_workbook_plus_2796
-- name    : lean_workbook_plus_2796
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/dd7e1d78-1e16-4ff3-a2ec-1d43bf06e3d3
-- statement:
--   Prove that: $\sqrt{sin^{2}x+\frac{1}{sin^{2}x}}+\sqrt{sin^{2}y+\frac{1}{sin^{2}y}}+\sqrt{cos^{2}x+\frac{1}{cos^{2}x}}+\sqrt{cos^{2}y+\frac{1}{cos^{2}y}}\geq 2\sqrt{10}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2796 : ∀ x y : ℝ, (Real.sqrt (sin x ^ 2 + 1 / sin x ^ 2) + Real.sqrt (sin y ^ 2 + 1 / sin y ^ 2) + Real.sqrt (cos x ^ 2 + 1 / cos x ^ 2) + Real.sqrt (cos y ^ 2 + 1 / cos y ^ 2)) ≥ 2 * Real.sqrt 10   :=  by sorry
