-- Prove2me | solution 1 for Heisenberg125.Heis.asum_cons
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:12:13.880797+00:00
-- url     : https://prove2.me/submissions/853bf1d1-b939-4b3b-8c4f-cadbf3839a66

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} (g : Heis p) (L) : asum (g :: L) = g.a + asum L := by
  simp only [asum, List.map_cons, List.sum_cons]
