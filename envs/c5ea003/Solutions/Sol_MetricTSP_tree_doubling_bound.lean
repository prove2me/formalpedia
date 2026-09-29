-- Prove2me | solution 1 for MetricTSP.tree_doubling_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T19:56:44.139555+00:00
-- url     : https://prove2.me/submissions/c7781151-6809-4b0b-8697-d6573552255e

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_graph_cost
import Definitions.Def_MetricTSP_tour_vector
import Theorems.Thm_MetricTSP_cheap_connected_subgraph
import Theorems.Thm_MetricTSP_tour_of_connected
import Theorems.Thm_MetricTSP_tsp_opt_le_tour_cost
import Theorems.Thm_MetricTSP_tour_vector_held_karp

namespace MetricTSP

/-- **Tree doubling against the LP.** For every Held–Karp feasible point there is a
cheap connected subgraph; doubling and shortcutting it yields a tour of at most twice
its cost, so the optimal tour is at most twice every LP objective, hence at most twice
the LP value. -/
theorem tree_doubling (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) :
    tspOpt c ≤ 2 * hkValue c := by
  have hkey : ∀ t ∈ {t : ℝ | ∃ x : Fin n → Fin n → ℝ, IsHeldKarp x ∧
      t = (1 / 2) * ∑ u, ∑ v, c u v * x u v}, tspOpt c / 2 ≤ t := by
    rintro t ⟨x, hx, rfl⟩
    obtain ⟨G, hG, hcost⟩ := cheap_connected_subgraph n hn c hc x hx
    obtain ⟨π, hπ⟩ := tour_of_connected n (by omega) c hc G hG
    have h3 := tsp_opt_le_tour_cost n c hc π
    linarith
  have hne : {t : ℝ | ∃ x : Fin n → Fin n → ℝ, IsHeldKarp x ∧
      t = (1 / 2) * ∑ u, ∑ v, c u v * x u v}.Nonempty :=
    ⟨(1 / 2) * ∑ u, ∑ v, c u v * tourVec 1 u v, tourVec 1,
      tour_vector_held_karp n hn 1, rfl⟩
  have hinf : tspOpt c / 2 ≤ hkValue c := by
    unfold hkValue
    exact le_csInf hne hkey
  linarith

end MetricTSP

open MetricTSP

theorem solution (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) :
    tspOpt c ≤ 2 * hkValue c :=
  MetricTSP.tree_doubling n hn c hc
