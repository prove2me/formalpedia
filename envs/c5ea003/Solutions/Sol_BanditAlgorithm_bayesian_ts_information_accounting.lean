-- Prove2me | solution 1 for BanditAlgorithm.bayesian_ts_information_accounting
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T22:09:05.583261+00:00
-- url     : https://prove2.me/submissions/6eea5092-7482-42a3-a33b-ed0bf5837f4c

import Theorems.Thm_BanditAlgorithm_bayesian_ts_squared_regret_information_bound

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BanditAlgorithm

theorem _root_.solution {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (t : Fin n) (a : Fin k), X t a ∈ Set.Icc (0 : ℝ) 1)
    {π : BanditPolicy k} (hπ : IsBayesianTSPolicy Q π) :
    ∃ δ info : Fin n → ℝ,
      bayesianAdversarialRegret Q π = ∑ t, δ t ∧
      (∀ t, δ t ^ 2 ≤ ((k : ℝ) / 2) * info t) ∧
      ∑ t, info t ≤ Real.log k := by
  obtain ⟨δ, hregret, hsquares⟩ :=
    bayesian_ts_squared_regret_information_bound Q hQ hπ
  have hk : (0 : ℝ) < k := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  refine ⟨δ, fun t ↦ (2 / (k : ℝ)) * δ t ^ 2, hregret, ?_, ?_⟩
  · intro t
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk
    rw [show ((k : ℝ) / 2) * ((2 / (k : ℝ)) * δ t ^ 2) = δ t ^ 2 by
      field_simp]
  · calc
      ∑ t, (2 / (k : ℝ)) * δ t ^ 2 =
          (2 / (k : ℝ)) * ∑ t, δ t ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (2 / (k : ℝ)) * (((k : ℝ) / 2) * Real.log k) := by
        gcongr
      _ = Real.log k := by
        field_simp

end BanditAlgorithm
