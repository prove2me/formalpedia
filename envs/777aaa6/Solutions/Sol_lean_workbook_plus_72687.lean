-- Prove2me | solution 1 for lean_workbook_plus_72687
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:08.204169+00:00
-- url     : https://prove2.me/submissions/bd85fb22-067b-42c3-a5d9-102c79445284

import Mathlib

set_option autoImplicit false

theorem solution ⦃a b : ℝ⦄ (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a ^ 3 + b ^ 3) ^ 2 ≥ a ^ 6 + b ^ 6 + 2 * a ^ 3 * b ^ 3 := by
  exact le_of_eq (by ring)
