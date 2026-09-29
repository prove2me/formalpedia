-- Prove2me | solution 1 for RLHF.variance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:08:13.039301+00:00
-- url     : https://prove2.me/submissions/dc058ecb-2d7d-48ea-a1bb-210a13a80efe

import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
open RLHF Finset in
theorem solution {Ω : Type*} [Fintype Ω] {p : Ω → ℝ} (hp : IsDist p) (f : Ω → ℝ) :
    0 ≤ variance p f := by
  unfold variance
  refine Finset.sum_nonneg (fun y _ => ?_)
  exact mul_nonneg (hp.nonneg y) (sq_nonneg _)
