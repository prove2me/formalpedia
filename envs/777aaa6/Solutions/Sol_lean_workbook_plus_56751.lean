-- Prove2me | solution 1 for lean_workbook_plus_56751
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:38.582228+00:00
-- url     : https://prove2.me/submissions/b2c82f9e-5591-4110-8a9d-59a0dd5dcb2d

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (h1 : a + b ≥ 0) (h2 : b + c ≥ 0) (h3 : a + c ≥ 0) : a + b + c ≥ (|a| + |b| + |c|) / 3   := by
  have ha : |a| ≤ a + b + c := abs_le.mpr ⟨by linarith, by linarith⟩
  have hb : |b| ≤ a + b + c := abs_le.mpr ⟨by linarith, by linarith⟩
  have hc : |c| ≤ a + b + c := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

#print axioms solution
