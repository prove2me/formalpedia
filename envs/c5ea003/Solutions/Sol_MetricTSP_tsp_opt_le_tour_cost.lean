-- Prove2me | solution 1 for MetricTSP.tsp_opt_le_tour_cost
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T19:56:43.693771+00:00
-- url     : https://prove2.me/submissions/30ad42b3-0468-4c70-a71e-24559a374da5

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

lemma metric_nonneg3 {n : ℕ} {c : Fin n → Fin n → ℝ} (hc : IsMetricCost c) (u v : Fin n) :
    0 ≤ c u v := by
  obtain ⟨hsym, hdiag, htri⟩ := hc
  have h := htri u v u
  rw [hdiag u, hsym v u] at h
  linarith

theorem tsp_le_tour (n : ℕ) (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (π : Equiv.Perm (Fin n)) : tspOpt c ≤ tourCost c π := by
  have hc0 : ∀ u v, 0 ≤ c u v := metric_nonneg3 hc
  have hbdd : BddBelow {t : ℝ | ∃ ρ : Equiv.Perm (Fin n), t = tourCost c ρ} := by
    refine ⟨0, ?_⟩
    rintro t ⟨ρ, rfl⟩
    unfold tourCost
    apply Finset.sum_nonneg
    intro i _
    exact hc0 _ _
  unfold tspOpt
  refine csInf_le hbdd ?_
  exact ⟨π, rfl⟩

end MetricTSP

open MetricTSP

theorem solution (n : ℕ) (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (π : Equiv.Perm (Fin n)) : tspOpt c ≤ tourCost c π :=
  MetricTSP.tsp_le_tour n c hc π
