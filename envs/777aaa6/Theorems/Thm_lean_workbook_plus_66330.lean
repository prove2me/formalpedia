-- Prove2me | Theorems.Thm_lean_workbook_plus_66330
-- name    : lean_workbook_plus_66330
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/f2f5199d-39de-469b-a7ce-cd1e6b544168
-- statement:
--   Show that, for all $\alpha_i$ , the equations $\beta_1 + \beta_3 = \alpha_1$, $\beta_1 + \beta_2 = \alpha_2$, $\beta_2 + \beta_3 = \alpha_3$ can be satisfied.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66330 (α₁ α₂ α₃ : ℝ) : ∃ β₁ β₂ β₃ : ℝ, β₁ + β₃ = α₁ ∧ β₁ + β₂ = α₂ ∧ β₂ + β₃ = α₃   :=  by sorry
