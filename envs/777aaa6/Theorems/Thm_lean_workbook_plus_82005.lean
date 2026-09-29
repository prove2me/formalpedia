-- Prove2me | Theorems.Thm_lean_workbook_plus_82005
-- name    : lean_workbook_plus_82005
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/375903bc-3a6a-4826-8ea0-5fceda1d332b
-- statement:
--   Prove that the interval $[0,\ 1]$ is invariant for $f(x)=4x(1-x)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82005 (f : ℝ → ℝ) (hf: f = fun x => 4 * x * (1 - x)) : ∀ x ∈ Set.Icc 0 1, f x ∈ Set.Icc 0 1   :=  by sorry
