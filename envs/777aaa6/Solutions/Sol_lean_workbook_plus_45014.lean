-- Prove2me | solution 1 for lean_workbook_plus_45014
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:45:33.192724+00:00
-- url     : https://prove2.me/submissions/bb6d9795-a650-4e04-80f4-8d0015bf1afc

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℤ) (h : a ≡ 1 [ZMOD 3] ∨ a ≡ 2 [ZMOD 3]) : a^2 ≡ 1 [ZMOD 3] := by
  rcases h with h | h
  · simpa only [one_pow] using h.pow 2
  · exact (h.pow 2).trans (by decide : (2:ℤ)^2 ≡ 1 [ZMOD 3])
