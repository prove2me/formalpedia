-- Prove2me | Theorems.Thm_lean_workbook_plus_6187
-- name    : lean_workbook_plus_6187
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3ed5694f-86d7-408c-bd66-0537b0652a30
-- statement:
--   Prove that if $\frac{x^2-1}{y+1}+\frac{y^2-1}{x+1}$ is an integer for integers $x$ and $y$, then $\frac{x^2-1}{y+1}$ and $\frac{y^2-1}{x+1}$ are also integers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6187 (x y : ℤ) (h : ∃ k : ℤ, (x^2 - 1) / (y + 1) + (y^2 - 1) / (x + 1) = k) :
    ∃ k₁ k₂ : ℤ, (x^2 - 1) / (y + 1) = k₁ ∧ (y^2 - 1) / (x + 1) = k₂   :=  by sorry
