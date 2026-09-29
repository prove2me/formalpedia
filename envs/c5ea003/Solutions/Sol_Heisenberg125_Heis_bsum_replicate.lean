-- Prove2me | solution 1 for Heisenberg125.Heis.bsum_replicate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T18:31:15.933985+00:00
-- url     : https://prove2.me/submissions/d14692d3-e494-4676-8cc2-80937c7fa36d

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_LowerBound
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} (n : ℕ) (g : Heis p) :
    bsum (List.replicate n g) = (n : ZMod p) * g.b := by
  -- the list of coordinates is `n` copies of `g.b`
  simp [bsum, List.map_replicate, List.sum_replicate, nsmul_eq_mul]
