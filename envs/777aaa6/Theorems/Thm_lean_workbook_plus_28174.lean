-- Prove2me | Theorems.Thm_lean_workbook_plus_28174
-- name    : lean_workbook_plus_28174
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/dd016d64-f144-4085-a2f2-e67d7b3c3838
-- statement:
--   Given $ \alpha=(\pi-(\beta+\gamma))$ , prove that \n\n $ \cos \alpha=\cos (\pi-(\beta+\gamma))=-\cos(\gamma+\beta))$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28174 (α β γ : ℝ) : α = π - (β + γ) → cos α = -cos (γ + β)   :=  by sorry
