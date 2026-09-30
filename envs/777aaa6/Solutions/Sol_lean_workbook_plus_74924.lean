-- Prove2me | solution 1 for lean_workbook_plus_74924
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:15:40.887428+00:00
-- url     : https://prove2.me/submissions/b0492998-2ed4-41f8-ab40-bca838605a3c

import Mathlib
set_option autoImplicit false

theorem solution {a b n : ℤ} (h : a ≡ b [ZMOD n]) (k : ℕ) : a ^ k ≡ b ^ k [ZMOD n]   := by
  induction' k with k ih
  simpa only [pow_zero] using (show (1 : ℤ) ≡ 1 [ZMOD n] from rfl)
  simpa only [pow_succ] using ih.mul h

#print axioms solution
