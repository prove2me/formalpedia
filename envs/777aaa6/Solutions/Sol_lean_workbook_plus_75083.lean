-- Prove2me | solution 1 for lean_workbook_plus_75083
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:52:21.282857+00:00
-- url     : https://prove2.me/submissions/204d0f58-4521-49e9-9ba8-2e5680d84163

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution (n : ℤ) (h : n > 0 ∧ Odd n) :
    ∃ m : ℤ, n * (n + 2) = 4 * m ^ 2 - 1 := by
  obtain ⟨k, hk⟩ := h.2
  refine ⟨k + 1, ?_⟩
  rw [hk]
  ring

#print axioms solution
