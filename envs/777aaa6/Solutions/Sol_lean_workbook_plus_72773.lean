-- Prove2me | solution 1 for lean_workbook_plus_72773
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:21.714447+00:00
-- url     : https://prove2.me/submissions/064108b8-3d9c-4c30-9a41-adf181682644

import Mathlib
set_option autoImplicit false

theorem solution (x : ℕ → ℕ) (h1 : x 10 = 91)
    (h2 : ∀ n, x (n + 1) = 2 * n + x n) : x 9 = 73 := by
  have h := h2 9
  norm_num at h
  omega

#print axioms solution
