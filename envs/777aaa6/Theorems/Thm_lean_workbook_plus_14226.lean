-- Prove2me | Theorems.Thm_lean_workbook_plus_14226
-- name    : lean_workbook_plus_14226
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/bc03314c-f062-42f2-9216-1e3e7ee5bf30
-- statement:
--   Therefore, $\beta=\dfrac{\pi}{3},\alpha=\dfrac{\pi}{3}-x,\gamma=\dfrac{\pi}{3}+x (x>0)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14226  (x β α γ : ℝ)
  (h₀ : 0 < x)
  (h₁ : β = π / 3)
  (h₂ : α = π / 3 - x)
  (h₃ : γ = π / 3 + x) :
  α + β + γ = π ∧ α = π / 3 - x ∧ β = π / 3 ∧ γ = π / 3 + x   :=  by sorry
