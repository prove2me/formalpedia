-- Prove2me | solution 1 for lean_workbook_plus_76098
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:12:02.988327+00:00
-- url     : https://prove2.me/submissions/11c91fb6-1164-4d77-85c0-49da8fd1e6fc

import Mathlib
set_option autoImplicit false

theorem solution : ∀ a : ℝ, -1 ≤ a ∧ a ≤ 1 → (1 + |a| + a^2)^3 ≥ (1 + |a|)^3 * (1 + |a|^3)   := by
  intro a _ha
  have hgap : (1 + |a| + a ^ 2) ^ 3 - (1 + |a|) ^ 3 * (1 + |a| ^ 3) =
      |a| ^ 2 * (3 + 5 * |a| + 3 * |a| ^ 2) := by
    rw [← sq_abs a]
    ring
  have hnonneg : 0 ≤ |a| ^ 2 * (3 + 5 * |a| + 3 * |a| ^ 2) := by positivity
  nlinarith only [hgap, hnonneg]

#print axioms solution
