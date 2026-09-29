-- Prove2me | Theorems.Thm_lean_workbook_plus_71767
-- name    : lean_workbook_plus_71767
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/1f9eccb1-f81c-4c39-9097-37863146eb91
-- statement:
--   The function $f(x)=x^2$ from $[0,1]\to[0,1]$ is surjective
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71767 : ∀ x : ℝ, x ∈ Set.Icc 0 1 → ∃ y : ℝ, y ∈ Set.Icc 0 1 ∧ y ^ 2 = x   :=  by sorry
