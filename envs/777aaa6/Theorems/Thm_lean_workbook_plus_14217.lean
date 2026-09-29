-- Prove2me | Theorems.Thm_lean_workbook_plus_14217
-- name    : lean_workbook_plus_14217
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/8d88755c-d79a-46d6-93ef-dd9161bfaf5b
-- statement:
--   f(x)=a $\forall x\notin\{-\sqrt 3,+\sqrt 3\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14217 (a : ℝ) (f : ℝ → ℝ) (hf: f = fun x => if x ≠ -Real.sqrt 3 ∧ x ≠ Real.sqrt 3 then a else 0) : ∀ x, x ≠ -Real.sqrt 3 ∧ x ≠ Real.sqrt 3 → f x = a   :=  by sorry
