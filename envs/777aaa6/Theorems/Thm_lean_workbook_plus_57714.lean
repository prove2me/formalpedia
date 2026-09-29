-- Prove2me | Theorems.Thm_lean_workbook_plus_57714
-- name    : lean_workbook_plus_57714
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/4d49ed3e-6008-4305-99a3-9657b3be7466
-- statement:
--   Prove that the equation for the tension at the end of the rope (T_2) in terms of the tension at the other end (T_1) and the angle (θ) is $T_2 = T_1 \left(1+\frac{\mu\theta}{n}\right)^n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57714 (n : ℕ) (μ : ℝ) (θ : ℝ) (T₁ : ℝ) : ∃ T₂, T₂ = T₁ * (1 + μ * θ / n)^n   :=  by sorry
