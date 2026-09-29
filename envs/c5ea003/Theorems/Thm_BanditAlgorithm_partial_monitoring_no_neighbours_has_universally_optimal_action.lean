-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_no_neighbours_has_universally_optimal_action
-- name    : BanditAlgorithm.partial_monitoring_no_neighbours_has_universally_optimal_action
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T16:15:45.12145+00:00
-- url     : https://prove2.me/theorems/8c674345-9d7a-43d1-8eb5-a83252b7cf8e
-- title:
--   No neighbouring cells implies a universally optimal action
-- statement:
--   Let $G$ be a finite partial-monitoring game with at least one action and at least one outcome. If the cell decomposition of the outcome simplex has no pair of neighbouring Pareto-optimal actions, then some action $a$ is optimal for every outcome individually:
--
--   $$
--   \exists a\;\forall b,i,\qquad L_{a i} \le L_{b i}.
--   $$
--
--   Equivalently, the cell of $a$ is the whole outcome simplex. This is the finite-polyhedral geometric core of the trivial class in the partial-monitoring classification theorem.
--
--   **Formalization Note** Nonemptiness of the finite action and outcome sets is explicit because the source treats these as nonempty by convention.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Section 37.8, Theorem 37.22, printed p. 503 (PDF p. 511); https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.partial_monitoring_no_neighbours_has_universally_optimal_action
    {k d : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊)
    (hk : 0 < k) (hd : 0 < d)
    (h : ¬ HasNeighbouringActions G) :
    ∃ a : Fin k, ∀ b : Fin k, ∀ i : Fin d, G.L a i ≤ G.L b i := by
  sorry
