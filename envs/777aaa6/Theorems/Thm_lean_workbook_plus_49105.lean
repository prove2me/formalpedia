-- Prove2me | Theorems.Thm_lean_workbook_plus_49105
-- name    : lean_workbook_plus_49105
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/58d8839c-f8ba-4ae0-8c98-dd2f82958678
-- statement:
--   Prove that \(\mathop{\lim }_{x \to 0}\frac{{\sin x}}{x}= 1\) without using Euclidean Geometry.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49105 (x : ℝ) (hx : x ≠ 0) : ∃ ε : ℝ, 0 < ε ∧ abs (sin x / x - 1) < ε   :=  by sorry
