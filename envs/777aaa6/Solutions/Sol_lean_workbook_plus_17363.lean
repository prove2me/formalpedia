-- Prove2me | solution 1 for lean_workbook_plus_17363
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:14.655001+00:00
-- url     : https://prove2.me/submissions/34d5b7b5-4bbb-4a26-97ac-33326b704bde

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n k : ℕ) (h₁ : 1 ≤ k ∧ k ≤ n) : k * (n - k + 1) ≥ n := by
  have he : n=k+(n-k) := by omega
  have hp := Nat.mul_le_mul_right (n-k) h₁.1
  nlinarith
