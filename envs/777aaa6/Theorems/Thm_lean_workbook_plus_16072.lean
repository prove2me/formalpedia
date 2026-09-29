-- Prove2me | Theorems.Thm_lean_workbook_plus_16072
-- name    : lean_workbook_plus_16072
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/ef3859c8-cff2-4b55-8c31-0f66ee41a3b0
-- statement:
--   Prove the identity \(\cos 2kx \cdot \cos x = \frac {1}{2}\left[\cos \left(2k - 1\right)x + \cos \left(2k + 1\right)x\right]\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16072 : ∀ k x, Real.cos (2 * k * x) * Real.cos x = (1 / 2) * (Real.cos ((2 * k - 1) * x) + Real.cos ((2 * k + 1) * x))   :=  by sorry
