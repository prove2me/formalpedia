-- Prove2me | Theorems.Thm_lean_workbook_plus_37352
-- name    : lean_workbook_plus_37352
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/1da4a1e0-e008-4e55-8291-a429ff0cc666
-- statement:
--   Using the definition of the Cauchy limit of a function, prove that \n\n $$\lim_{x\to 0 }x\sin \frac{1}{x}=0$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37352 : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ≠ 0 ∧ |x| < δ → |x * sin (1/x)| < ε   :=  by sorry
