-- Prove2me | Theorems.Thm_lean_workbook_plus_57421
-- name    : lean_workbook_plus_57421
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/2441fb7e-bf2c-47de-b469-fab8dfe20f9f
-- statement:
--   Prove the equality $a\alpha+b\beta+c\gamma = (a+b+c)(\alpha+\beta+\gamma)$ where $\alpha = bc-a^2$ , $\beta = ca-b^2$ , $\gamma = ab-c^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57421 (a b c α β γ : ℝ) (h₁ : α = b * c - a ^ 2) (h₂ : β = c * a - b ^ 2) (h₃ : γ = a * b - c ^ 2) : a * α + b * β + c * γ = (a + b + c) * (α + β + γ)   :=  by sorry
