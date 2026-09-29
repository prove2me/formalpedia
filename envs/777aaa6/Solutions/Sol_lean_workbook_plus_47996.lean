-- Prove2me | solution 1 for lean_workbook_plus_47996
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:16:56.361781+00:00
-- url     : https://prove2.me/submissions/43ad04de-b6b8-4565-b412-a5891743aa66

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ {a a' m : ℕ}, a ≡ a' [ZMOD m] → ∀ n : ℕ, a ^ n ≡ a' ^ n [ZMOD m] := by
  intro a a' m h n
  exact_mod_cast h.pow n
