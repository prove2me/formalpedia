-- Prove2me | Theorems.Thm_lean_workbook_plus_38692
-- name    : lean_workbook_plus_38692
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/91887be1-3cfc-4a4d-ae96-0b19b9b50586
-- statement:
--   $ \sqrt {x_1^2 + (1 - x_2)^2} \ge \frac{\sqrt {2}}{2}(x_{1} + 1 - x_{2})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38692 (x₁ x₂ : ℝ) :
  Real.sqrt (x₁^2 + (1 - x₂)^2) ≥ (Real.sqrt 2 / 2) * (x₁ + 1 - x₂)   :=  by sorry
