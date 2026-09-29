-- Prove2me | solution 1 for Heisenberg125.Heis.asum_append
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T17:26:00.006472+00:00
-- url     : https://prove2.me/submissions/80946f74-18b8-4561-a670-92169c749cfb

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_LowerBound
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} (L M : List (Heis p)) : asum (L ++ M) = asum L + asum M := by
  -- a coordinate sum of a concatenation splits
  simp [asum, List.map_append, List.sum_append]
