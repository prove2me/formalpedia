-- Prove2me | solution 1 for RLHF.variance_sub_mad_sq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T12:51:05.331922+00:00
-- url     : https://prove2.me/submissions/d7fec007-e79a-4ba8-897c-c2601c675a7a

import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore

set_option autoImplicit false
set_option maxHeartbeats 400000

open RLHF Finset

open RLHF in
/-- **The target, verbatim.** -/
theorem solution {Ω : Type*} [Fintype Ω] {p : Ω → ℝ} (hp : IsDist p) (f : Ω → ℝ) :
    variance p f - mad p f ^ 2 = ∑ y, p y * (|f y - mean p f| - mad p f) ^ 2 := by
  have hvar : variance p f = ∑ y, p y * |f y - mean p f| ^ 2 :=
    Finset.sum_congr rfl (fun y _ => by rw [sq_abs])
  have hexp : ∀ y : Ω, p y * (|f y - mean p f| - mad p f) ^ 2
      = p y * |f y - mean p f| ^ 2 - 2 * mad p f * (p y * |f y - mean p f|)
        + mad p f ^ 2 * p y := fun y => by ring
  rw [hvar, Finset.sum_congr rfl (fun y _ => hexp y), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp.total, ← mad]
  ring
