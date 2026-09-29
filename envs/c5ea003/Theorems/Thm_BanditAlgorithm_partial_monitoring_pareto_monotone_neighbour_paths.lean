-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_pareto_monotone_neighbour_paths
-- name    : BanditAlgorithm.partial_monitoring_pareto_monotone_neighbour_paths
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T18:12:11.00838+00:00
-- url     : https://prove2.me/theorems/73bc1332-f883-4978-9843-f1a03c83178f
-- title:
--   Monotone neighbour paths in the Pareto-cell graph
-- statement:
--   For a finite partial-monitoring game with at least two actions and one outcome, one can select a nonempty set $S$ of Pareto-optimal representatives whose cells cover the outcome simplex. Hence every finite outcome sequence has a best action in $S$. Moreover, for each mixed outcome $\lambda$, there is a root in $S$ and, from every $b\in S$, a simple path of at most $k$ neighbouring actions to the root along which the $\lambda$-expected loss never increases.\n\nThis is the finite path form of connectedness of the Pareto-cell adjacency graph and the loss-monotone in-tree used by the water-transfer operator.\n\n**Formalization Note** Paths are indexed by `Fin (m+1)` and have at most $k$ edges, making the later estimator sum and its uniform norm bound explicit.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Cambridge University Press (2020), Lemma 37.7 printed p. 484 and Lemma 37.21 printed pp. 501–502. https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame

open scoped BigOperators

theorem BanditAlgorithm.partial_monitoring_pareto_monotone_neighbour_paths
    {k d : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k) (hd : 0 < d) :
    ∃ S : Finset (Fin k),
      S.Nonempty ∧
      (∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t)) ∧
      ∀ lam : Fin d → ℝ, lam ∈ stdSimplex ℝ (Fin d) →
        ∃ root ∈ S, ∀ b ∈ S,
          ∃ m : ℕ, ∃ path : Fin (m + 1) → Fin k,
            m ≤ k ∧ path 0 = b ∧ path (Fin.last m) = root ∧
            (∀ t, path t ∈ S) ∧
            ∀ t : Fin m,
              NeighbouringActions G (path t.castSucc) (path t.succ) ∧
              ∑ i : Fin d, G.L (path t.succ) i * lam i ≤
                ∑ i : Fin d, G.L (path t.castSucc) i * lam i := by sorry
