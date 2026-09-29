-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_globally_observable_bounded_vector_estimator
-- name    : BanditAlgorithm.partial_monitoring_globally_observable_bounded_vector_estimator
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T20:10:35.69698+00:00
-- url     : https://prove2.me/theorems/ddb10f0d-aee6-4411-a309-020b862e46b7
-- title:
--   Bounded vector estimator for globally observable games
-- statement:
--   Let $G$ be a finite globally observable partial-monitoring game with at least two actions and at least one outcome. Then there is a nonempty Pareto comparator set $S$, a finite constant $V\ge0$, and a vector loss estimator $f$ on $S$ such that
--
--   $$
--   |f(a,\sigma,b)|\le V
--   $$
--
--   for every played action $a$, signal $\sigma$, and comparator $b$. The set $S$ contains a best fixed action for every finite outcome sequence.
--
--   The result packages the path-sum construction needed in the hard-game upper bound: sum one global edge estimator along bounded-length paths in the neighbourhood graph.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Chapter 37, Lemma 37.7 (p. 484), global observability Eq. (37.3) (p. 486), and the path-sum construction used in Theorem 37.16 (printed pp. 497–498). https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringAlgorithm26

open scoped BigOperators

theorem BanditAlgorithm.partial_monitoring_globally_observable_bounded_vector_estimator
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k) (hd : 0 < d)
    (hglo : GloballyObservable G) :
    ∃ S : Finset (Fin k), ∃ V : ℝ,
      S.Nonempty ∧ 0 ≤ V ∧
      (∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t)) ∧
      ∃ f : Fin k → 𝕊 → Fin k → ℝ,
        PMVectorEstimatorOn G S f ∧ ∀ a σ b, |f a σ b| ≤ V := by sorry
