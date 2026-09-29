-- Prove2me | solution 1 for lean_workbook_plus_18730
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:54:58.884993+00:00
-- url     : https://prove2.me/submissions/06aa4bef-bb4f-476d-8a57-994c449316a2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (k : ℕ) (h₁ : 4 < k) : 5 * k ^ 4 + 500 * k > (k + 1) ^ 4 + 100 * k + 100 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 5 ≤ k)
  ring_nf
  omega
