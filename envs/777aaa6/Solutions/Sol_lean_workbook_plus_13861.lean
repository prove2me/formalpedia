-- Prove2me | solution 1 for lean_workbook_plus_13861
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:30:42.207736+00:00
-- url     : https://prove2.me/submissions/1a22e479-ffc8-4449-a5fa-970b5548e736

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b c m : ℤ} (h₁ : a ≡ b [ZMOD m]) : a + c ≡ b + c [ZMOD m] := by
  exact h₁.add_right c
