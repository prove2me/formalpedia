-- Prove2me | solution 2 for RLHF.one_le_tiltNorm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:31:01.076558+00:00
-- url     : https://prove2.me/submissions/4d7a1b08-212f-4822-8874-69b8233cc45c

import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFMeanAbsoluteDeviation
open RLHF Finset in
theorem solution {Ω : Type*} [Fintype Ω] {β : ℝ} {r p : Ω → ℝ}
    (hp : IsDist p) : 1 ≤ tiltNorm β r p := by
  obtain ⟨hnn, hsum⟩ := hp
  show (1 : ℝ) ≤ ∑ y, p y * Real.exp ((r y - mean p r) / β)
  have hmean : mean p r = ∑ y, p y * r y := rfl
  -- the centred reward has `p`-mean zero, for any `β` (including `β = 0`)
  have hzero : ∑ y, p y * ((r y - mean p r) / β) = 0 := by
    have hstep : ∀ y : Ω, p y * ((r y - mean p r) / β)
        = (p y * r y - mean p r * p y) * β⁻¹ := by
      intro y; rw [div_eq_mul_inv]; ring
    calc ∑ y, p y * ((r y - mean p r) / β)
        = ∑ y, (p y * r y - mean p r * p y) * β⁻¹ := Finset.sum_congr rfl fun y _ => hstep y
      _ = (∑ y, (p y * r y - mean p r * p y)) * β⁻¹ := (Finset.sum_mul _ _ _).symm
      _ = ((∑ y, p y * r y) - ∑ y, mean p r * p y) * β⁻¹ := by
            rw [Finset.sum_sub_distrib]
      _ = ((∑ y, p y * r y) - mean p r * ∑ y, p y) * β⁻¹ := by rw [Finset.mul_sum]
      _ = 0 := by rw [hsum, ← hmean]; ring
  -- `exp x ≥ 1 + x` pointwise, weighted by `p y ≥ 0`
  have hpt : ∀ y : Ω, p y * (1 + (r y - mean p r) / β)
      ≤ p y * Real.exp ((r y - mean p r) / β) := by
    intro y
    refine mul_le_mul_of_nonneg_left ?_ (hnn y)
    linarith [Real.add_one_le_exp ((r y - mean p r) / β)]
  calc (1 : ℝ) = (∑ y, p y) + ∑ y, p y * ((r y - mean p r) / β) := by rw [hsum, hzero]; ring
    _ = ∑ y, (p y + p y * ((r y - mean p r) / β)) := (Finset.sum_add_distrib).symm
    _ = ∑ y, p y * (1 + (r y - mean p r) / β) := Finset.sum_congr rfl fun y _ => by ring
    _ ≤ ∑ y, p y * Real.exp ((r y - mean p r) / β) := Finset.sum_le_sum fun y _ => hpt y
