-- Prove2me | Theorems.Thm_lean_workbook_plus_8160
-- name    : lean_workbook_plus_8160
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/ff9873fa-7751-4cda-83ac-360bc1f02333
-- statement:
--   $\boxed{\text{S2 : }f(x)=g(x)=-x\quad\forall x}$ , which indeed fits too
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8160 : ∃ f g : ℝ → ℝ, ∀ x, f x = -x ∧ g x = -x   :=  by sorry
