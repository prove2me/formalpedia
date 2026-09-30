-- Prove2me | solution 1 for lean_workbook_plus_82317
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:01.112527+00:00
-- url     : https://prove2.me/submissions/9a3adb34-d990-457e-a458-92041cdc6252

import Mathlib
set_option autoImplicit false

theorem solution {x : ℤ} (h : x ≡ 2 [ZMOD 4]) : x^2 ≡ 0 [ZMOD 4] := by
  have hp := h.pow 2
  exact hp.trans (by decide)

#print axioms solution
