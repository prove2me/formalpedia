-- Prove2me | Theorems.Thm_lean_workbook_plus_17036
-- name    : lean_workbook_plus_17036
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/99307721-04f3-49fd-adae-52066c8d851f
-- statement:
--   $\boxed{f(x)=0, \forall x\in\mathbb Z}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17036 (f : ℤ → ℤ) (hf: f = fun x => 0) : ∀ x, f x = 0   :=  by sorry
