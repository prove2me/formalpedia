-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_hard_rpow_two_thirds_upper_bound_discrete_signals
-- name    : BanditAlgorithm.partial_monitoring_hard_rpow_two_thirds_upper_bound_discrete_signals
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T15:36:32.91402+00:00
-- url     : https://prove2.me/theorems/71691e5d-e9e4-47b8-82ce-ba197e515e37
-- title:
--   Theorems 37.15–37.16: $O(n^{2/3})$ upper bound for hard games
-- statement:
--   Let $G=(L,\Phi)$ be a finite globally observable but not locally observable partial-monitoring game with a finite discrete signal alphabet. Then there are a game-dependent constant $C_G>0$ and a horizon $N_G$ such that
--
--   $$
--   R_n^*(G) \le C_G n^{2/3} \qquad \text{for every }n\ge N_G.
--   $$
--
--   This is the upper half of the hard-game classification. Algorithm 26 and the global-observability estimate for its exploration–stability objective yield an explicit $O((v_{glo}kn)^{2/3}(\log k)^{1/3})$ bound, whose fixed-game factors are absorbed into $C_G$.
--
--   **Formalization Note** Lean writes the fractional power as `Real.rpow`, denoted by `^` with a real exponent in the displayed formal statement.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Chapter 37, Theorem 37.15 and Algorithm 26 on printed pp. 494–495, Theorem 37.16 and its proof on printed pp. 496–498, and Section 37.8 on printed p. 503 (PDF pp. 502–511), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.partial_monitoring_hard_rpow_two_thirds_upper_bound_discrete_signals
    {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊)
    (h : GloballyObservable G ∧ ¬ LocallyObservable G) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      pmMinimaxRegret G n ≤ C * (n : ℝ) ^ ((2 : ℝ) / 3) := by
  sorry
