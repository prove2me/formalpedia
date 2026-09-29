-- Prove2me | solution 1 for RLHF.mad_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:26:33.252462+00:00
-- url     : https://prove2.me/submissions/9c6ec7d0-c30d-4c3b-911a-c37a709611f9

import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
open RLHF Finset in
theorem solution {Ω : Type*} [Fintype Ω] {p : Ω → ℝ} (hp : IsDist p) (f : Ω → ℝ) :
    0 ≤ mad p f := by
  obtain ⟨hnn, -⟩ := hp
  exact Finset.sum_nonneg fun y _ => mul_nonneg (hnn y) (abs_nonneg _)
