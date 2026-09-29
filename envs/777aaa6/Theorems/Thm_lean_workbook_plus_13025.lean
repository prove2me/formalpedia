-- Prove2me | Theorems.Thm_lean_workbook_plus_13025
-- name    : lean_workbook_plus_13025
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/89596dc7-5a40-44b8-a759-737ecb63e011
-- statement:
--   Given $ \sin \alpha = \frac{3}{5}$ and $ \cos \alpha = \frac{4}{5}$, find $ \cos \left(\frac{\pi}{2}-2 \alpha\right)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13025 (α : ℝ) (h₁ : 0 < α ∧ α < π/2) (h₂ : sin α = 3/5) (h₃ : cos α = 4/5) : cos (π/2 - 2 * α) = 7/25   :=  by sorry
