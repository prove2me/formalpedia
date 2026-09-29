-- Prove2me | Theorems.Thm_BanditAlgorithm_gittins_policy_dominates_of_epsilon_stopping_calibration
-- name    : BanditAlgorithm.gittins_policy_dominates_of_epsilon_stopping_calibration
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T03:05:32.681512+00:00
-- url     : https://prove2.me/theorems/2d046162-cd3e-44ce-9ce7-57e42ae6f333
-- title:
--   Multi-arm dominance from epsilon-optimal Gittins stopping calibration
-- statement:
--   Consider a discounted $k$-armed Markov bandit on a standard Borel state space, with transition kernel $P$, measurable reward $r$, and discount factor $\alpha\in(0,1)$. Assume discounted absolute rewards are integrable. Suppose the single-arm index is calibrated in the following epsilon-optimal sense: from every state $y$ and for every $\varepsilon>0$, some admissible stopping time has discounted reward ratio greater than $g(y)-\varepsilon$.
--
--   If $\pi^*$ always activates an arm with maximal current Gittins index, then for every competing policy $\pi$ and initial state vector $x$,
--
--   $$
--   V^{\pi}(x)\le V^{\pi^*}(x).
--   $$
--
--   This theorem isolates the genuinely multi-arm part of the Gittins index theorem: the prevailing-charge comparison and the Hardy--Littlewood interleaving argument. The single-arm optimal-stopping calibration is exposed as an explicit reusable hypothesis.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), proof of Theorem 35.9, printed pp.451--453: Part 1 (prevailing charge), Part 2 (interleaving prevailing charges), and Lemma 35.10.

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_GittinsIndex

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittins_policy_dominates_of_epsilon_stopping_calibration
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (hcal : ∀ (y : S) (ε : ℝ), 0 < ε →
      ∃ τ : (ℕ → S) → ℕ∞,
        IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
        gittinsIndex P r α y - ε <
          (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P y) /
            (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω
              ∂markovChainMeasure P y))
    (πstar : MarkovBanditPolicy k S) (hπ : IsGittinsIndexPolicy P r α πstar)
    (x : Fin k → S) :
    ∀ π : MarkovBanditPolicy k S,
      markovBanditDiscountedValue P r α π x ≤
        markovBanditDiscountedValue P r α πstar x := by
  sorry
