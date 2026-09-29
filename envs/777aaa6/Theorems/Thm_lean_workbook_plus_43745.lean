-- Prove2me | Theorems.Thm_lean_workbook_plus_43745
-- name    : lean_workbook_plus_43745
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/21589127-e57e-489e-964f-51d7aa6d50e8
-- statement:
--   Prove that the function $f(x) = 9x-x^{3}$ is not injective.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43745 : ¬ Function.Injective (fun x : ℝ => 9*x - x^3)   :=  by sorry
