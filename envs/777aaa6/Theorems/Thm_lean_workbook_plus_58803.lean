-- Prove2me | Theorems.Thm_lean_workbook_plus_58803
-- name    : lean_workbook_plus_58803
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/fa9d5fd3-144f-4318-bed9-cd99a7bdb2c8
-- statement:
--   In the first case, $p=n-13\land q=n-1\implies f(x)=(x-n+13)(x-n+1)$ , thus $f(n+1)=14\cdot 2=28$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58803  (n p q : ℤ)
  (f : ℤ → ℤ)
  (h₀ : ∀ x, f x = (x - p) * (x - q))
  (h₁ : p = n - 13)
  (h₂ : q = n - 1)
  (h₃ : n + 1 = 15) :
  f (n + 1) = 28   :=  by sorry
