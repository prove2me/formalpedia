-- Prove2me | solution 1 for lean_workbook_plus_71935
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:30:57.361111+00:00
-- url     : https://prove2.me/submissions/c8042dc6-255a-46d7-847f-e9df1645e818

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false

theorem solution {a b : ℕ} (h₁ : a ∣ b) : (2 ^ a - 1) ∣ (2 ^ b - 1) := by
  obtain ⟨k, rfl⟩ := h₁
  rw [pow_mul]
  simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2 ^ a) 1 k

#print axioms solution
