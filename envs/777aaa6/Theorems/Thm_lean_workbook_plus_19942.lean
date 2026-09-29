-- Prove2me | Theorems.Thm_lean_workbook_plus_19942
-- name    : lean_workbook_plus_19942
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/b50ee23b-5b63-4959-8e06-4b5e27aef104
-- statement:
--   The question is to show that the equation has at least a root in $[0,2]$ and I exactly proved this.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19942 (f : ℝ → ℝ) (hf: f = fun (x:ℝ) => x^2 - 2) : ∃ x, x ∈ Set.Icc 0 2 ∧ f x = 0   :=  by sorry
