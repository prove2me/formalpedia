-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_locally_observable_upper_bound_discrete_signals
-- name    : BanditAlgorithm.partial_monitoring_locally_observable_upper_bound_discrete_signals
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T17:47:00.081096+00:00
-- url     : https://prove2.me/theorems/3b37f665-5efc-4ae3-ad91-815c5466b5ee
-- title:
--   Locally observable regret upper bound for discrete signals
-- statement:
--   Let G be a locally observable finite partial-monitoring game with at least two actions, discrete finite signals, and losses in [0,1]. Then there is a constant C>0 such that for every horizon n,
--
--   $$
--   R_n^*(G)\leq C\,\max\{1,v_{\mathrm{loc}}(G)\}\,k^{3/2}\sqrt{n\log k}.
--   $$
--
--   The discrete-signal measurability hypothesis makes the history-dependent Algorithm 26 policy measurable. This is the unit-loss upper-bound component used in the easy regime of the classification theorem.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Chapter 37, Theorems 37.15 and 37.17, printed pp. 494--502, https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.partial_monitoring_locally_observable_upper_bound_discrete_signals
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k)
    (hL : ∀ a i, G.L a i ∈ Set.Icc (0 : ℝ) 1)
    (hloc : LocallyObservable G) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      pmMinimaxRegret G n ≤
        C * max 1 (pmLocObsConst G) * (k : ℝ) ^ ((3 : ℝ) / 2) *
          Real.sqrt (n * Real.log k) := by
  sorry
