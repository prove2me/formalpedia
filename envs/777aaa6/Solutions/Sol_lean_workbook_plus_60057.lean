-- Prove2me | solution 1 for lean_workbook_plus_60057
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:08:55.520267+00:00
-- url     : https://prove2.me/submissions/afba60a8-b130-4e0a-992f-99a378978e0f

import Mathlib
set_option autoImplicit false

theorem solution (x y t : ℝ) (ht : t = x*y) : (x + y^2019) * (x^2019 + y) ≥ t * (t^1009 + 1)^2   := by
  have hgap : (x + y^2019) * (x^2019 + y) - t * (t^1009 + 1)^2 =
      (x^1010 - y^1010)^2 := by
    rw [ht]
    ring
  apply sub_nonneg.mp
  rw [hgap]
  exact sq_nonneg _

#print axioms solution
