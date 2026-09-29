-- Prove2me | Theorems.Thm_lean_workbook_plus_79560
-- name    : lean_workbook_plus_79560
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/b1a582fc-f0ba-4214-bf9d-b6448720257a
-- statement:
--   Find all function $ f$ which is continuous and defined on all positive real numbers such that:\n$f(f(x)) = x,\ f(x + 1) = \frac {f(x)}{f(x) + 1}\ \forall x > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79560 : ∃ f : ℝ → ℝ, ContinuousOn f (Set.Ioi 0) ∧ ∀ x > 0, f (f x) = x ∧ f (x + 1) = f x / (f x + 1)   :=  by sorry
