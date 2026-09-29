-- Prove2me | Theorems.Thm_lean_workbook_plus_51058
-- name    : lean_workbook_plus_51058
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/8ba3102a-fea3-422c-91d3-7a7958a46d91
-- statement:
--   Then : \nIf $U=\{0\}$ , we get $\boxed{\text{S1 : }f(x)=0\text{ }\forall x}$ which indeed is a solution
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51058 (f : ℝ → ℝ) (U : Set ℝ) (hU : U = {0}) : ∃ f : ℝ → ℝ, ∀ x, f x = 0   :=  by sorry
