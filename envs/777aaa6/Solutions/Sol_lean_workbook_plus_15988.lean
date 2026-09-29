-- Prove2me | solution 1 for lean_workbook_plus_15988
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:30:13.604389+00:00
-- url     : https://prove2.me/submissions/184fecc6-10f4-498b-8b3e-82146074f387

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) : 2 ^ (n - 1) ≡ (-1) ^ (n - 1) [ZMOD 3] := by
  have h : (2:ℤ) ≡ -1 [ZMOD 3] := by norm_num [Int.ModEq]
  exact_mod_cast h.pow (n-1)
