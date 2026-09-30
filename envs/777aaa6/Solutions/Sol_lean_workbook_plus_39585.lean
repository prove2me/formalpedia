-- Prove2me | solution 1 for lean_workbook_plus_39585
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:29:55.657898+00:00
-- url     : https://prove2.me/submissions/9fdb2efc-8bed-47ca-8ebb-d0a8c1a81dd7

import Mathlib.Data.Int.ModEq

set_option autoImplicit false

theorem solution (a m n x : ℕ) (hm : m > 0) (hn : n > 0)
    (hmn : Nat.Coprime m n) :
    x ≡ a [ZMOD m] ∧ x ≡ a [ZMOD n] → x ≡ a [ZMOD m * n] := by
  exact (Int.modEq_and_modEq_iff_modEq_mul (by simpa using hmn)).mp

#print axioms solution
