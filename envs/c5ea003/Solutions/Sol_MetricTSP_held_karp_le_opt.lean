-- Prove2me | solution 1 for MetricTSP.held_karp_le_opt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T19:22:41.25586+00:00
-- url     : https://prove2.me/submissions/218fa633-913e-4911-8d96-936c4d853cb5

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_tour_vector
import Theorems.Thm_MetricTSP_tour_vector_held_karp
import Theorems.Thm_MetricTSP_tour_vector_cost
import Theorems.Thm_MetricTSP_hk_value_le_of_feasible

namespace MetricTSP

/-- Validity of the Held–Karp relaxation: every Hamiltonian tour induces a feasible
point of the subtour-elimination LP whose objective is the tour cost, so the LP
value is at most the optimal tour cost. -/
theorem hk_le_opt (n : ℕ) (hn : 3 ≤ n)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    hkValue c ≤ tspOpt c := by
  unfold tspOpt
  refine le_csInf ⟨tourCost c 1, 1, rfl⟩ ?_
  rintro t ⟨π, rfl⟩
  have h1 := hk_value_le_of_feasible n c hc (tourVec π) (tour_vector_held_karp n hn π)
  have h2 := tour_vector_cost n hn c hc.1 π
  rw [h2] at h1
  linarith

end MetricTSP

open MetricTSP

theorem solution (n : ℕ) (hn : 3 ≤ n)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    hkValue c ≤ tspOpt c :=
  MetricTSP.hk_le_opt n hn c hc
