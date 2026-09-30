-- Prove2me | solution 1 for lean_workbook_plus_53124
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:40:32.414271+00:00
-- url     : https://prove2.me/submissions/adea7215-67c4-4b49-8914-1d86dba6d494

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

theorem solution (f : ℤ → ℤ)
    (h : ∀ a b : ℤ, f (9 * f a + b) = 9 * a + b) : f 0 = 0 := by
  have hz := h 0 (-9 * f 0)
  have hc : 9 * f 0 + -9 * f 0 = 0 := by linarith
  rw [hc] at hz
  linarith

theorem identity_classification (f : ℤ → ℤ)
    (h : ∀ a b : ℤ, f (9 * f a + b) = 9 * a + b) : f = id := by
  have hz := solution f h
  funext x
  simpa [hz] using h 0 x

#print axioms solution
#print axioms identity_classification
