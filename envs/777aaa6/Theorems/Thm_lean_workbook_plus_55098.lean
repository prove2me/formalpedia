-- Prove2me | Theorems.Thm_lean_workbook_plus_55098
-- name    : lean_workbook_plus_55098
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/be828ddb-3cd5-4729-81c8-5661feac6dbf
-- statement:
--   Let $w=e^{i\pi /11}$, show that $1+w^2+w^4+\ldots +w^{20}=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55098 (w : ℂ) (hw : w = exp (I * π / 11)) :
  ∑ k in Finset.range 10, w^(2 * k) = 0   :=  by sorry
