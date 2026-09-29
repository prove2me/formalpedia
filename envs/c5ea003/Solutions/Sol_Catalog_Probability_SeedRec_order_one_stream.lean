-- Prove2me | solution 1 for Catalog.Probability.SeedRec.order_one_stream
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:49:42.726338+00:00
-- url     : https://prove2.me/submissions/c3d427f9-202a-4590-aef6-489dacd455f4

import Mathlib
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGSeedRecovery
import Definitions.Def_Probability_PRNGEnumerationL1
import Definitions.Def_Probability_PRNGComplexityHierarchy
import Definitions.Def_Probability_PRNGRouterCapacity
open Catalog.Probability.SeedRec Finset in
theorem solution {K : Type*} [Field K] (c σ : Fin 1 → K) (t : ℕ) :
    (lfsrPRNG c).stream σ t = c 0 ^ t * σ 0 := by
  have hstep1 : ∀ τ : Fin 1 → K, lfsrStep c τ = fun _ => c 0 * τ 0 := by
    intro τ
    funext i
    fin_cases i
    simp [lfsrStep]
  have hit : ∀ k : ℕ, (lfsrStep c)^[k] σ = fun _ => c 0 ^ k * σ 0 := by
    intro k
    induction k with
    | zero =>
      funext i
      fin_cases i
      simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, hstep1]
      funext i
      simp [pow_succ]
      ring
  simp [PRNG.stream, lfsrPRNG, lfsrOut, hit]
