-- Prove2me | solution 1 for Heisenberg125.Heis.csum_replicate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T18:37:19.187063+00:00
-- url     : https://prove2.me/submissions/67527c44-05bc-494c-ba40-4f0799a15ec3

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_LowerBound
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} (n : ℕ) (g : Heis p) :
    csum (List.replicate n g) = (n : ZMod p) * g.c := by
  -- the list of coordinates is `n` copies of `g.c`
  simp [csum, List.map_replicate, List.sum_replicate, nsmul_eq_mul]
