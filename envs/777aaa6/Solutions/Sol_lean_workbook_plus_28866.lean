-- Prove2me | solution 1 for lean_workbook_plus_28866
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:13.293071+00:00
-- url     : https://prove2.me/submissions/d0733dd7-0dba-45f9-baf2-249ec418ae00

import Mathlib
set_option autoImplicit false

theorem solution : ∀ n ≥ 0, (4^(2*n + 1) + 3^(n + 2)) % 13 = 0   := by
  intro n hn
  clear hn
  induction' n with n IH
  rfl
  rw [show 4 ^ (2 * (n + 1) + 1) = 4 ^ (2 * n + 1) * 4 ^ 2 by ring_nf]
  rw [show 3 ^ (n + 1 + 2) = 3 ^ (n + 2) * 3 by ring_nf]
  omega

#print axioms solution
