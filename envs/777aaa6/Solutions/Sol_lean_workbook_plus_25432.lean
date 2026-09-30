-- Prove2me | solution 1 for lean_workbook_plus_25432
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:44:46.737616+00:00
-- url     : https://prove2.me/submissions/c81fad19-93c9-4a94-ba28-eb4ab7b218df

import Mathlib
set_option autoImplicit false

theorem solution (n m a : ℕ) (hn: n^5 ≡ 1 [ZMOD a]) : n^(5*m) ≡ 1 [ZMOD a]   := by
  rw [pow_mul]
  simpa [pow_mul] using hn.pow m

#print axioms solution
