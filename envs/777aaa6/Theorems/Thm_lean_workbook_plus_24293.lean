-- Prove2me | Theorems.Thm_lean_workbook_plus_24293
-- name    : lean_workbook_plus_24293
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/91b062ad-a9ee-474b-a5df-1c9790dd80e5
-- statement:
--   Let $\alpha, \beta, \gamma, \delta$ be the roots of the equation $x^4+px^3+qx^2+rx+s=0$ . Prove that $(\alpha\beta+\gamma\delta)(\beta\gamma+\alpha\delta)(\gamma\alpha+\beta\delta)=r^2-4qs+p^2s$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24293 (α β γ δ : ℂ) (p q r s : ℂ) (h : α + β + γ + δ = -p) (h' : α * β + α * γ + α * δ + β * γ + β * δ + γ * δ = q) (h'' : α * β * γ + α * β * δ + α * γ * δ + β * γ * δ = -r) (h''' : α * β * γ * δ = s) : (α * β + γ * δ) * (β * γ + α * δ) * (γ * α + β * δ) = r^2 - 4*q*s + p^2 * s   :=  by sorry
