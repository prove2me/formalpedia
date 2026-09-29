-- Prove2me | Theorems.Thm_lean_workbook_plus_6877
-- name    : lean_workbook_plus_6877
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/ccd17c0b-a5c3-4746-8dfb-65b3670c8acf
-- statement:
--   Let $ u_n=x_nx_{n+1}$\nWe have $ u_0=ab$ and $ u_n=\frac 12(1+u_{n-1})$ and so $ u_n=1+\frac{ab-1}{2^n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6877  (a b : ℝ)
  (n : ℕ)
  (u : ℕ → ℝ)
  (h₀ : u 0 = a * b)
  (h₁ : ∀ n, u (n + 1) = (1 + u n) / 2) :
  u n = 1 + (a * b - 1) / 2 ^ n   :=  by sorry
