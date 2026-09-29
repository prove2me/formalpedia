-- Prove2me | Theorems.Thm_lean_workbook_plus_75013
-- name    : lean_workbook_plus_75013
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/2b8c97db-aac3-423e-a06c-40cd6063a100
-- statement:
--   So $h_{1}=x_{1}+p=x_{1}+2\sqrt{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75013 (x₁ h₁ : ℝ) (p : ℝ) (hp : p = 2 * Real.sqrt 2) : h₁ = x₁ + p ↔ h₁ = x₁ + 2 * Real.sqrt 2   :=  by sorry
