-- Prove2me | solution 1 for lean_workbook_plus_72464
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:47.500973+00:00
-- url     : https://prove2.me/submissions/46cfea9f-c280-4e37-84e4-3a2218bf39e0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℝ)
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : ∀ i, a i > 0)
  (h₂ : ∀ i, a (i + 1) + a (i + 2) ≠ 0)
  (h₃ : n = (Finset.range n).sum (fun i => a i / (a (i + 1) + a (i + 2)))) :
  n / 2 ≤ (Finset.range n).sum (fun i => a i / (a (i + 1) + a (i + 2))) := by
  (intros; linarith)
