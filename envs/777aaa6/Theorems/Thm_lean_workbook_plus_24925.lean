-- Prove2me | Theorems.Thm_lean_workbook_plus_24925
-- name    : lean_workbook_plus_24925
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/c48036e5-f41f-4a5d-82e3-c2b16b2d0fdb
-- statement:
--   Hence $f(n)=nf(1)$ so $f(f(n))=n=f(n)f(1)=nf(1)^2$ so $f(1)^2=1\implies f(1)=1$ so $\boxed{f(n)=n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24925  (n : ℕ)
  (f : ℕ → ℕ)
  (h₀ : ∃ n, f n ≠ n)
  (h₁ : ∀ n, f (f n) = n * f 1)
  (h₂ : ∃ n, f n ≠ n * f 1) :
  f 1 = 1 ∧ ∀ n, f n = n   :=  by sorry
