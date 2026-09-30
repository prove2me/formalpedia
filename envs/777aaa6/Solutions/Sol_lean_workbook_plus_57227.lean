-- Prove2me | solution 1 for lean_workbook_plus_57227
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:21:50.520572+00:00
-- url     : https://prove2.me/submissions/562b0313-0d82-4b9e-ae3c-2d436654c0d3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

theorem solution : ∀ x y : ℚ, x > 0 → y > 0 → ∃ n : ℕ, y < n * x := by
  intro x y hx hy
  obtain ⟨n, hn⟩ := exists_nat_gt (y / x)
  exact ⟨n, (div_lt_iff₀ hx).mp hn⟩

#print axioms solution
