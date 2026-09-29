-- Prove2me | Theorems.Thm_lean_workbook_plus_17398
-- name    : lean_workbook_plus_17398
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/19c57bad-e90c-4b61-8f2a-44b85cf6f8ea
-- statement:
--   $\boxed{\text{S2 : }f(x)=2\cos ax\text{ }\forall x\ge 0}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17398 (f : ℝ → ℝ) (a : ℝ) (hf: f = fun x => if x >= 0 then 2 * Real.cos (a * x) else 0) : ∀ x, x >= 0 → f x = 2 * Real.cos (a * x)   :=  by sorry
