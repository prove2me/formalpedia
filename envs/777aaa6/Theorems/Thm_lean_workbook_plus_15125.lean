-- Prove2me | Theorems.Thm_lean_workbook_plus_15125
-- name    : lean_workbook_plus_15125
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/b3b8ee6b-6e3e-45c8-a9cb-a628c0350078
-- statement:
--   Prove that $\lim_{x \to 0^+} 0^x = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15125 : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x > 0 ∧ x < δ → |0^x| < ε   :=  by sorry
