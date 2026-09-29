-- Prove2me | solution 1 for lean_workbook_plus_11519
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:13:30.856299+00:00
-- url     : https://prove2.me/submissions/31e6ec79-64bf-433d-8cc3-49709e668432

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution (n : ℕ) (a : ℕ → ℝ) (t : ℝ) (h₁ : ∀ i, a (i + 1) - a i ≥ t) : ∀ i, a (i + 1) - a 1 ≥ i * t := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have hi := h₁ (i + 1)
    push_cast
    nlinarith
