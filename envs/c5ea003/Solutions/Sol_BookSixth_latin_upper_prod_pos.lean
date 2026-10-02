-- Prove2me | solution 1 for BookSixth.latin_upper_prod_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T00:04:48.916765+00:00
-- url     : https://prove2.me/submissions/e979dd06-34bf-46ce-a19b-08501479f8d6

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n : ℕ) :
    0 < ∏ k ∈ Finset.Icc 1 n, (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ)) := by
  apply Finset.prod_pos
  intro k hk
  apply Real.rpow_pos_of_pos
  positivity
