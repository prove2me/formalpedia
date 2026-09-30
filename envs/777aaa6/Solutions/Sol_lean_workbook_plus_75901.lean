-- Prove2me | solution 1 for lean_workbook_plus_75901
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:07:21.33908+00:00
-- url     : https://prove2.me/submissions/088324cc-62f6-4b77-8b36-7f5fe18c79c1

import Mathlib
set_option autoImplicit false

theorem solution (m n : ℕ) (a : Fin m → Fin n → NNReal) : ∑ j : Fin n, ∑ i : Fin m, a i j = ∑ i : Fin m, ∑ j : Fin n, a i j   := by
  exact Finset.sum_comm

#print axioms solution
