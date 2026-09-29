-- Prove2me | Theorems.Thm_lean_workbook_plus_60257
-- name    : lean_workbook_plus_60257
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/8a9438bc-0eb1-43c8-84be-ed2f572153df
-- statement:
--   Assume $a = b = c = 0$ and you will get $f(0) = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60257  (a b c : ℝ)
  (f : ℝ → ℝ)
  (h₀ : a = 0 ∧ b = 0 ∧ c = 0)
  (h₁ : f a + b + c = 0)
  : f 0 = 0   :=  by sorry
