-- Prove2me | Theorems.Thm_lean_workbook_plus_18112
-- name    : lean_workbook_plus_18112
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/c3cbe033-7b15-4552-b674-069bac1e5cca
-- statement:
--   Let $y=(x+1)$ ; we get that this is $1+\cdots+y^3-(1+\cdots+y)=z^2-z$ where $z=\frac{y(y+1)}{2}$ . Thus $z^2-z=4290$ yields the positive solution $z=66$ , so $y(y+1)=132$ . This gives the positive solution $y=11$ , so $\boxed{x=10}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18112  (x : ℕ)
  (h₀ : 0 < x)
  (h₁ : ∑ k in Finset.Icc 1 (x + 1), k^3 - ∑ k in Finset.Icc 1 x, k = 4290) :
  x = 10   :=  by sorry
