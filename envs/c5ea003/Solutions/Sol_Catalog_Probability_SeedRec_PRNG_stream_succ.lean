-- Prove2me | solution 1 for Catalog.Probability.SeedRec.PRNG.stream_succ
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:58:36.808983+00:00
-- url     : https://prove2.me/submissions/6831e705-3cc9-4151-af57-0127d239d0f4

import Mathlib
import Definitions.Def_Probability_PRNGSeedRecovery
open Catalog.Probability.SeedRec in
theorem solution {S : Type*} {α : Type*} (g : PRNG S α) (s : S) (t : ℕ) :
    g.stream s (t + 1) = g.stream (g.step s) t := by
  simp only [PRNG.stream]
  rw [Function.iterate_succ_apply]
