-- Prove2me | solution 1 for lean_workbook_plus_71095
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:20.640481+00:00
-- url     : https://prove2.me/submissions/1511cebb-26b3-4c93-a375-38e6d573b7bb

import Mathlib
set_option autoImplicit false

theorem solution (f : ℕ → ℝ)
    (hf : ∀ n, 1 < n → f n = (n + 1) / (n - 1)) : f 100 = 101 / 99 := by
  have h := hf 100 (by norm_num)
  norm_num at h
  exact h

#print axioms solution
