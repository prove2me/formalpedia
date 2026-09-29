-- Prove2me | Theorems.Thm_lean_workbook_plus_80977
-- name    : lean_workbook_plus_80977
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/cad89685-979e-43f4-b997-4c5612fe76a8
-- statement:
--   Prove that $4(a^2+b^2+2ab\cos\theta)\ge (a+b)^2(1+1+2\cos\theta)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80977 (a b : ℝ) : 4 * (a ^ 2 + b ^ 2 + 2 * a * b * Real.cos θ) ≥ (a + b) ^ 2 * (1 + 1 + 2 * Real.cos θ)   :=  by sorry
