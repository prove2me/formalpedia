-- Prove2me | Theorems.Thm_lean_workbook_plus_19442
-- name    : lean_workbook_plus_19442
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/c0e73440-4e87-4dfe-97de-3ebccf79dfb5
-- statement:
--   $2x-1=u^2\Rightarrow~|u+1|+|u-1|=2\Rightarrow~|u|\le 1\Rightarrow~x\in[1/2,1]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19442 (x : ℝ) (u : ℝ) (h₁ : 2 * x - 1 = u ^ 2) (h₂ : abs (u + 1) + abs (u - 1) = 2) (h₃ : abs u ≤ 1) : 1 / 2 ≤ x ∧ x ≤ 1   :=  by sorry
