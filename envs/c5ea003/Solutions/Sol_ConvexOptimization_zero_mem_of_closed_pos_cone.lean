-- Prove2me | solution 1 for ConvexOptimization.zero_mem_of_closed_pos_cone
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T04:48:17.913505+00:00
-- url     : https://prove2.me/submissions/94db4c52-7b95-46b3-8d3c-8cd21283ac24

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution {d : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKclosed : IsClosed K)
    (hKcone : ∀ t : ℝ, 0 < t → ∀ y ∈ K, t • y ∈ K) (hne : K.Nonempty) :
    (0 : EuclideanSpace ℝ (Fin d)) ∈ K := by
  obtain ⟨y, hy⟩ := hne
  have htend : Filter.Tendsto (fun k : ℕ => (1 / (k + 1 : ℝ)) • y) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun k : ℕ => (1 / (k + 1 : ℝ))) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h0.smul_const y
  refine hKclosed.mem_of_tendsto htend (Filter.Eventually.of_forall fun k => ?_)
  exact hKcone _ (by positivity) y hy
