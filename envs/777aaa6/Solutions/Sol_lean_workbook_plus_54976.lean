-- Prove2me | solution 1 for lean_workbook_plus_54976
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:04:22.196634+00:00
-- url     : https://prove2.me/submissions/d594b8e6-d65f-4d62-b713-1dc5a2a1714a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.ModEq

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (p : ℕ) (hp : p ≡ 1 [ZMOD 6]) : ∃ m : ℕ, p = 6*m + 1 := by
  rw [Int.ModEq] at hp
  refine ⟨p / 6, ?_⟩
  omega
