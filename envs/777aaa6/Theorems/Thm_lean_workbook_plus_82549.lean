-- Prove2me | Theorems.Thm_lean_workbook_plus_82549
-- name    : lean_workbook_plus_82549
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/08b9eb6b-0798-44e2-8932-233f8dca461c
-- statement:
--   Given $\alpha\cdot\beta + \beta \cdot \gamma + \gamma\cdot \alpha = 0$ and $\alpha\cdot\beta\cdot \gamma=1$, prove that $\frac{1}{\gamma}=\frac{1}{-\alpha}+\frac{1}{-\beta}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82549 (α β γ : ℝ) (h₁ : α * β + β * γ + γ * α = 0) (h₂ : α * β * γ = 1) : 1 / γ = 1 / -α + 1 / -β   :=  by sorry
