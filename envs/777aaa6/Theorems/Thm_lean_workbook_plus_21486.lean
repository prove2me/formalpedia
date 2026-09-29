-- Prove2me | Theorems.Thm_lean_workbook_plus_21486
-- name    : lean_workbook_plus_21486
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/22d1421e-7955-43eb-8cef-839387a199ba
-- statement:
--   $\boxed{\text{S3 : }f(x)=2\cosh ax\text{ }\forall x\ge 0}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21486 (f : ℝ → ℝ) (a : ℝ) (hf: f = fun x => 2 * Real.cosh (a * x)) : ∀ x ≥ 0, f x = 2 * Real.cosh (a * x)   :=  by sorry
