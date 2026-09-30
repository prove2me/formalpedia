-- Prove2me | solution 1 for lean_workbook_plus_66588
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:39.988104+00:00
-- url     : https://prove2.me/submissions/9b1c78fa-4dbc-4ab5-a1b3-9f49abb6aec9

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) : 9 * (a^3 + b^3 + c^3) ≥ (a + b + c)^3 ↔ 8 * (a^3 + b^3 + c^3) ≥ 3 * (a + b) * (b + c) * (c + a)   := by
  ring_nf
  exact ⟨fun h => by linarith [h], fun h => by linarith [h]⟩

#print axioms solution
