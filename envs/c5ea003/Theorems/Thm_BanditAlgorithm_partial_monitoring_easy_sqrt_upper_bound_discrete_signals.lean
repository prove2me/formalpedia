-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_easy_sqrt_upper_bound_discrete_signals
-- name    : BanditAlgorithm.partial_monitoring_easy_sqrt_upper_bound_discrete_signals
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T15:36:28.52863+00:00
-- url     : https://prove2.me/theorems/a71d634c-6705-4e58-873e-4e2fea9eff77
-- title:
--   Theorems 37.15–37.17: $O(\sqrt n)$ upper bound for easy games
-- statement:
--   Let $G=(L,\Phi)$ be a finite locally observable partial-monitoring game with a finite discrete signal alphabet and at least one pair of neighbouring actions. Then there are a game-dependent constant $C_G>0$ and a horizon $N_G$ such that
--
--   $$
--   R_n^*(G) \le C_G\sqrt n \qquad \text{for every }n\ge N_G.
--   $$
--
--   This is the upper half of the easy-game classification. Algorithm 26 combines exponential weights with local loss-difference estimators; its factors depending on the fixed game, including $k$, $\log k$, and $v_{loc}$, are absorbed into $C_G$.
--
--   **Formalization Note** Arbitrary finite real loss matrices are reduced to the source’s $[0,1]$ normalization by an affine rescaling, which preserves observability and rescales minimax regret.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Chapter 37, Theorem 37.15 and Algorithm 26 on printed pp. 494–495, Theorem 37.17 on printed pp. 496 and 502, and the classification assembly in Section 37.8 on printed p. 503 (PDF pp. 502–511), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame
import Mathlib.Data.Real.Sqrt

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.partial_monitoring_easy_sqrt_upper_bound_discrete_signals
    {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊)
    (h : LocallyObservable G ∧ HasNeighbouringActions G) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      pmMinimaxRegret G n ≤ C * Real.sqrt n := by
  sorry
