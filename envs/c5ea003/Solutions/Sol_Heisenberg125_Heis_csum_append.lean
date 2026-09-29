-- Prove2me | solution 1 for Heisenberg125.Heis.csum_append
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T17:21:27.783258+00:00
-- url     : https://prove2.me/submissions/9cb4171c-080d-4fb8-8b0b-47455c5c235b

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_LowerBound
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} (L M : List (Heis p)) : csum (L ++ M) = csum L + csum M := by
  -- a coordinate sum of a concatenation splits
  simp [csum, List.map_append, List.sum_append]
