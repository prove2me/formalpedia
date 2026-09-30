-- Prove2me | solution 1 for lean_workbook_plus_35396
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:15:44.804217+00:00
-- url     : https://prove2.me/submissions/ee3ed8ae-5577-41c8-8748-5e1ee377c8ed

import Mathlib

set_option autoImplicit false

theorem even_expansion (k : Nat) :
    (2*k)^4 + (2*k)^3 + (2*k)^2 + 2*k + 1 =
      16*k^4 + 8*k^3 + 4*k^2 + 2*k + 1 := by ring

theorem odd_expansion (k : Nat) :
    (2*k+1)^4 + (2*k+1)^3 + (2*k+1)^2 + (2*k+1) + 1 =
      16*k^4 + 40*k^3 + 40*k^2 + 20*k + 5 := by ring

theorem solution : ¬ (∀ (n k : Nat), n = 2*k →
    n^4 + n^3 + n^2 + n + 1 =
      16*k^4 + 40*k^3 + 40*k^2 + 20*k + 5) := by
  intro h
  have hbad := h 2 1 rfl
  norm_num at hbad

#print axioms solution
