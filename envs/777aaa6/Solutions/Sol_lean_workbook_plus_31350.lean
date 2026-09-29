-- Prove2me | solution 1 for lean_workbook_plus_31350
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:55.451885+00:00
-- url     : https://prove2.me/submissions/96e66ab5-e7c2-4d31-a52b-6dd1e50ebfdf

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (f : ℕ → ℕ) (hf₁ : f 1 = f 0 + 1) (hf₂ : f 1 = (f 1)^3) (hf₃ : f 0 = (f 0)^3) : f 0 = 0 ∧ f 1 = 1 := by
  have h0 : f 0 ≤ 1 := by nlinarith [sq_nonneg (f 0)]
  have h1 : f 1 ≤ 1 := by nlinarith [sq_nonneg (f 1)]
  omega
