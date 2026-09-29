-- Prove2me | solution 1 for lean_workbook_plus_34668
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:33:23.85081+00:00
-- url     : https://prove2.me/submissions/6bb57fd2-222d-491b-b8c1-bed4eb6967eb

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (p q : ℕ) (hp : p.Prime) : p ∣ (q - 1) * (q ^ 2 + q + 1) → p ∣ q - 1 ∨ p ∣ q ^ 2 + q + 1 := by
  exact hp.dvd_mul.mp
