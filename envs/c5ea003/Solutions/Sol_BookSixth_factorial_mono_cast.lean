-- Prove2me | solution 1 for BookSixth.factorial_mono_cast
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T00:53:38.975197+00:00
-- url     : https://prove2.me/submissions/c48802c2-ad8b-40fa-afad-1c9341d1d505

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n m : ℕ) (h : n ≤ m) :
    (n.factorial : ℝ) ≤ (m.factorial : ℝ) := by
  exact_mod_cast Nat.factorial_le h
