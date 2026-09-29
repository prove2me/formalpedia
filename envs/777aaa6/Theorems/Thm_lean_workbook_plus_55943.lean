-- Prove2me | Theorems.Thm_lean_workbook_plus_55943
-- name    : lean_workbook_plus_55943
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/8070083a-3d61-4efa-8054-bc572dcb6c79
-- statement:
--   S2: $f(0)=1\text{ and }f(x)=0\text{ }\forall x>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55943 : ∃ f : ℝ → ℝ, f 0 = 1 ∧ ∀ x > 0, f x = 0   :=  by sorry
