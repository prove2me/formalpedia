-- Prove2me | solution 1 for lean_workbook_plus_21315
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:58.903733+00:00
-- url     : https://prove2.me/submissions/c550c93b-c3ce-472c-b975-40796ba563aa

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℤ) (h : a + b + c = 0) : ∃ k : ℤ, k^2 = 2 * a^4 + 2 * b^4 + 2 * c^4 := by
  refine ⟨a^2+b^2+c^2, ?_⟩
  have hc : c = -a-b := by omega
  rw [hc]
  ring
