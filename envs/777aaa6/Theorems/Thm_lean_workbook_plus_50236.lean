-- Prove2me | Theorems.Thm_lean_workbook_plus_50236
-- name    : lean_workbook_plus_50236
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/c5c354e1-50c1-4af9-ac0e-a3aab560321d
-- statement:
--   Since $ s \;\geq \; t\; \geq \;0$ and $ u \;\geq \; v\;>\;0$ , we have $ su \; \geq \; tv\;\geq \;0 \;\Rightarrow \; su \;-\; tv\; \geq \; 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50236  (s t u v : ℝ)
  (h₀ : 0 ≤ s ∧ 0 ≤ t)
  (h₁ : 0 < u ∧ 0 < v)
  (h₂ : s ≥ t)
  (h₃ : u ≥ v) :
  s * u - t * v ≥ 0   :=  by sorry
