-- Prove2me | solution 1 for lean_workbook_plus_6326
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:54:56.435579+00:00
-- url     : https://prove2.me/submissions/b692ea20-459d-4f3a-9cb3-5444faf16b4b

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℕ) (hx : ∃ k, k^2 = x) : ∃ k, k^2 = 4*x ∧ ∃ k, k^2 = 9*x := by
  rcases hx with ⟨k,rfl⟩
  refine ⟨2*k, ?_, 3*k, ?_⟩ <;> ring
