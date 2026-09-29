-- Prove2me | Theorems.Thm_lean_workbook_plus_8876
-- name    : lean_workbook_plus_8876
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/f00bb4a4-ebcb-44e0-b9fc-cc2eb3a3da6a
-- statement:
--   Suppose that $ f(1) = a$ . Then $ f(a) =-1$ , $ f(-1) =-a$ , and $ f(-a) = 1$ . We can see here that $ a$ can't be $ 0$ , $ 1$ , or $ -1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8876  (a : ℝ)
  (f : ℝ → ℝ)
  (h₀ : f 1 = a)
  (h₁ : f a = -1)
  (h₂ : f (-1) = -a)
  (h₃ : f (-a) = 1) :
  a ≠ 0 ∧ a ≠ 1 ∧ a ≠ -1   :=  by sorry
