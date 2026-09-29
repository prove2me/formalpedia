-- Prove2me | solution 1 for RLHF.sum_centered
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:56:07.511984+00:00
-- url     : https://prove2.me/submissions/920fdc90-bf45-433c-9034-8a6f22539442

import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore

open RLHF Finset

variable {Ω : Type*} [Fintype Ω]

theorem solution {p : Ω → ℝ} (hp : IsDist p) (f : Ω → ℝ) :
    ∑ y, p y * (f y - mean p f) = 0 := by
  simp_rw [mul_sub]
  rw [sum_sub_distrib]
  change mean p f - ∑ y, p y * mean p f = 0
  have hscale : ∑ y, p y * mean p f = mean p f * ∑ y, p y := by
    simp_rw [mul_comm (p _) (mean p f), ← mul_sum]
  rw [hscale, hp.total, mul_one, sub_self]
