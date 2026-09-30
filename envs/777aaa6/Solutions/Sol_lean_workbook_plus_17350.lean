-- Prove2me | solution 1 for lean_workbook_plus_17350
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:46:47.220817+00:00
-- url     : https://prove2.me/submissions/d8f06046-9ff5-4654-adce-c7007971e3b0

import Mathlib
set_option autoImplicit false

theorem solution (a b c d : ℝ) (habcd : a * b * c * d = 1) : 8 + (a^2 + b^2) * (c^2 + d^2) ≥ 3 * (a + b) * (c + d)   := by
  have bound : ∀ t : Real, 4 ≤ t^2 → 0 ≤ t^2-3*t+2 := by
    intro t ht
    by_cases ht0 : t ≤ 0
    · nlinarith only [ht, ht0]
    · have ht2 : 2 ≤ t := by nlinarith only [ht, not_le.mp ht0]
      have hp : 0 ≤ (t-1)*(t-2) :=
        mul_nonneg (by linarith only [ht2]) (by linarith only [ht2])
      nlinarith only [hp]
  have hu : 4 ≤ (a*c+b*d)^2 := by
    nlinarith only [habcd, sq_nonneg (a*c-b*d)]
  have hv : 4 ≤ (a*d+b*c)^2 := by
    nlinarith only [habcd, sq_nonneg (a*d-b*c)]
  have bu := bound (a*c+b*d) hu
  have bv := bound (a*d+b*c) hv
  nlinarith only [habcd, bu, bv]

#print axioms solution
