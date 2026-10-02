-- Prove2me | solution 1 for BookSixth.latin_lower_frac_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T00:07:52.225566+00:00
-- url     : https://prove2.me/submissions/8047142c-da21-4864-abde-77dcad053933

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n : ℕ) (hn : 0 < n) :
    0 < (n.factorial : ℝ) ^ (2*n) / (n : ℝ) ^ (n*n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply div_pos _ (pow_pos hnR _)
  apply pow_pos
  positivity
