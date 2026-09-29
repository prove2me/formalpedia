-- Prove2me | Theorems.Thm_lean_workbook_plus_80407
-- name    : lean_workbook_plus_80407
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/4b58ed7d-4562-43ee-9ce9-17bd0cc0fd10
-- statement:
--   So $f(x)=a^{\frac x3}$ $\forall x\ne 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80407 (f : ℝ → ℝ) (a : ℝ) (ha : a > 0) (hx: ∀ x, x ≠ 0 → f x = a ^ (x/3)) : ∃ x, x ≠ 0 ∧ f x = a ^ (x/3)   :=  by sorry
