-- Prove2me | Theorems.Thm_lean_workbook_plus_19217
-- name    : lean_workbook_plus_19217
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/54714948-a7a5-4e46-9c16-27152990c5ff
-- statement:
--   Let $f$ be a function with integer inputs and outputs such that $f(m)=f(m^2+n)$ for all integer pairs $(m,n).$ If $f(0)=0,$ find $\sum_{a=1}^{\infty} f(a).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19217 (f : ℤ → ℤ) (h₀ : f 0 = 0) (h₁ : ∀ m n, f m = f (m^2 + n)) : ∑ a in Finset.range 1, f a = 0   :=  by sorry
