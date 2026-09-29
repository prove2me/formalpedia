-- Prove2me | Theorems.Thm_lean_workbook_plus_63432
-- name    : lean_workbook_plus_63432
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/2f77f5c5-e24f-47f5-8937-3e7ccc4b2323
-- statement:
--   $\boxed{f(x)=-x^2, \forall x\in\mathbb Z}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63432 (f : ℤ → ℤ) (hf: f = fun x => -x^2) : ∀ x, f x = -x^2   :=  by sorry
