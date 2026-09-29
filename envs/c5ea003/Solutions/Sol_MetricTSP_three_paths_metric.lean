-- Prove2me | solution 1 for MetricTSP.three_paths_metric
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T20:14:12.46089+00:00
-- url     : https://prove2.me/submissions/e0d80520-da3e-4ad1-b34a-b75d32d1b429

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_three_paths

namespace MetricTSP

variable {k : ℕ}

/-- Structure of the coordinates: hubs are exactly the cities at positions `0` and
`k+1` and carry the sentinel path `3`; internal cities have positions in `[1, k]`
and a path among `0, 1, 2`. -/
lemma tpSpec (hk : 1 ≤ k) (v : Fin (3*k+2)) :
    (tpPath k v = 3 ∧ (tpPos k v = 0 ∨ tpPos k v = k+1))
    ∨ (tpPath k v < 3 ∧ 1 ≤ tpPos k v ∧ tpPos k v ≤ k) := by
  have hv := v.isLt
  unfold tpPath tpPos
  by_cases h : v.val = 0 ∨ v.val = 3*k+1
  · rw [if_pos h]
    left
    rcases h with h | h <;> rw [h] <;> simp <;> omega
  · rw [if_neg h]
    right
    push_neg at h
    have hmod : (v.val - 1) % k < k := Nat.mod_lt _ (by omega)
    have hdivlt : (v.val - 1) / k < 3 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    rw [if_neg h.1, if_neg h.2]
    omega

lemma tpDist_symm (hk : 1 ≤ k) (u v : Fin (3*k+2)) : tpDist k u v = tpDist k v u := by
  unfold tpDist
  simp only [Nat.dist]
  split_ifs with h1 h2 h2 <;> omega

lemma tpDist_self (v : Fin (3*k+2)) : tpDist k v v = 0 := by
  unfold tpDist
  rw [if_pos (Or.inr (Or.inr rfl))]
  simp [Nat.dist]

lemma tpDist_triangle (hk : 1 ≤ k) (u v w : Fin (3*k+2)) :
    tpDist k u w ≤ tpDist k u v + tpDist k v w := by
  have hu := tpSpec hk u
  have hv := tpSpec hk v
  have hw := tpSpec hk w
  unfold tpDist
  simp only [Nat.dist]
  split_ifs <;> omega

theorem three_paths_metric_thm (k : ℕ) (hk : 1 ≤ k) : IsMetricCost (tpCost k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    unfold tpCost
    rw [tpDist_symm hk]
  · intro v
    unfold tpCost
    rw [tpDist_self]
    simp
  · intro u v w
    unfold tpCost
    have := tpDist_triangle hk u v w
    push_cast
    exact_mod_cast this

end MetricTSP

open MetricTSP

theorem solution (k : ℕ) (hk : 1 ≤ k) : IsMetricCost (tpCost k) :=
  MetricTSP.three_paths_metric_thm k hk
