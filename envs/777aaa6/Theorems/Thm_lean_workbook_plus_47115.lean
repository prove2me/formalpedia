-- Prove2me | Theorems.Thm_lean_workbook_plus_47115
-- name    : lean_workbook_plus_47115
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/c4394482-d16b-4ce0-b10e-d35d3b9f6405
-- statement:
--   Prove that if x and y are rational numbers and k is irrational, then $x+ky=0 \implies x=y=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47115 (x y : ℚ) (k : ℝ) (h₁ : x + k * y = 0) (h₂ : ¬ k ∈ Set.range ((↑) : ℚ → ℝ)) : x = 0 ∧ y = 0   :=  by sorry
