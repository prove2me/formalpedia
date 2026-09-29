-- Prove2me | solution 1 for Heisenberg125.Heis.asum_replicate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T18:25:51.733773+00:00
-- url     : https://prove2.me/submissions/e5d829db-2704-4969-b781-2541e6490262

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_LowerBound
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} (n : ℕ) (g : Heis p) :
    asum (List.replicate n g) = (n : ZMod p) * g.a := by
  -- the list of coordinates is `n` copies of `g.a`
  simp [asum, List.map_replicate, List.sum_replicate, nsmul_eq_mul]
