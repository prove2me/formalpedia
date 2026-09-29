-- Prove2me | solution 1 for Catalog.Probability.SeedRec.PRNG.stream_add
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T21:05:45.233169+00:00
-- url     : https://prove2.me/submissions/6fb5d025-da9d-4929-8d3e-d9633172fbdd

import Mathlib
import Definitions.Def_Probability_PRNGSeedRecovery
open Catalog.Probability.SeedRec in
theorem solution {S : Type*} {α : Type*} (g : PRNG S α) (s : S) (t k : ℕ) :
    g.stream s (t + k) = g.stream (g.step^[t] s) k := by
  simp only [PRNG.stream]
  rw [← Function.iterate_add_apply, add_comm]
