-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_duplicate_free_pareto_cell_cover_ranked_descent
-- name    : BanditAlgorithm.partial_monitoring_duplicate_free_pareto_cell_cover_ranked_descent
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T19:09:01.087743+00:00
-- url     : https://prove2.me/theorems/3afd6754-7c1b-4bff-ab5f-593229b2f22e
-- title:
--   Ranked descent in a duplicate-free Pareto-cell cover
-- statement:
--   Let $S$ be a nonempty, duplicate-free family of Pareto-optimal actions whose cells cover the outcome simplex. For every mixed outcome $\lambda$, there are a root action and a natural-number rank such that every non-root $b\in S$ has a neighbouring successor $c\in S$ with
--
--   $$
--   \langle L_c,\lambda\rangle\leq\langle L_b,\lambda\rangle,
--   \qquad \operatorname{rank}(c)<\operatorname{rank}(b).
--   $$
--
--   The result supplies a terminating non-increasing in-tree in the Pareto-cell adjacency graph. It remains valid on cell boundaries, where distinct actions can tie under $\lambda$.
--
--   **Formalization Note** The explicit cell-cover hypothesis isolates the geometric content from the separate construction of a canonical Pareto representative set.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Cambridge University Press (2020), Lemma 37.7 p. 484, Exercise 37.10 p. 509, and Lemma 37.21 pp. 501–502, especially its finite-subsequence boundary argument. https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame

open scoped BigOperators

theorem BanditAlgorithm.partial_monitoring_duplicate_free_pareto_cell_cover_ranked_descent
    {k d : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (hd : 0 < d)
    (S : Finset (Fin k)) (hSne : S.Nonempty)
    (hpareto : ∀ a ∈ S, ParetoOptimalAction G a)
    (hunique : ∀ a ∈ S, ∀ b ∈ S,
      (∀ i, G.L a i = G.L b i) → a = b)
    (hcover : ∀ u, u ∈ stdSimplex ℝ (Fin d) →
      ∃ a ∈ S, u ∈ pmCell G a) :
    ∀ lam : Fin d → ℝ, lam ∈ stdSimplex ℝ (Fin d) →
      ∃ root ∈ S, ∃ rank : Fin k → ℕ,
        ∀ b ∈ S, b ≠ root →
          ∃ c ∈ S, NeighbouringActions G b c ∧
            ∑ i : Fin d, G.L c i * lam i ≤
              ∑ i : Fin d, G.L b i * lam i ∧
            rank c < rank b := by
  sorry
