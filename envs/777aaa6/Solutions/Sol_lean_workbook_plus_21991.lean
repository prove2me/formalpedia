-- Prove2me | solution 1 for lean_workbook_plus_21991
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:55:04.019802+00:00
-- url     : https://prove2.me/submissions/afbf5950-8b9e-4bfb-9349-0c16221bf196

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ p > 3, ∀ a : ℕ, a^4 ≡ 1 [ZMOD p] → (a^2 + 1) * (a^2 - 1) ≡ 0 [ZMOD p] := by
  intro p hp a h
  clear hp
  have he : ((a:ℤ)^2+1)*((a:ℤ)^2-1) = (a:ℤ)^4-1 := by ring
  rw [he]
  simpa only [sub_self] using h.sub (Int.ModEq.refl 1)
