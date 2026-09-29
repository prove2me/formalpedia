-- Prove2me | solution 1 for lean_workbook_plus_15038
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:45:32.11384+00:00
-- url     : https://prove2.me/submissions/3d55eca8-0d39-4e16-8527-cb4b56875345

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b c d : ℕ} (h : a^c ≡ b^c [ZMOD d]) : a^(2*c) ≡ b^(2*c) [ZMOD d] := by
  simpa only [← pow_mul, Nat.mul_comm c 2] using h.pow 2
