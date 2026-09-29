-- Prove2me | Theorems.Thm_BanditAlgorithm_gittins_index_policy_dominates
-- name    : BanditAlgorithm.gittins_index_policy_dominates
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T19:56:00.876947+00:00
-- url     : https://prove2.me/theorems/e9369d84-68e8-41e6-8f32-99261999234e
-- title:
--   A Gittins-index policy dominates every competing policy
-- statement:
--   Consider a discounted $k$-armed Markov bandit on a standard Borel state space. All arms evolve according to the same Markov kernel $P$, yield measurable reward $r$, and are discounted by $\alpha\in(0,1)$. Assume the expected discounted absolute reward of each single-arm chain is finite. If $\pi^*$ always activates an arm whose current state has maximal Gittins index, then for every competing policy $\pi$ and every initial state vector $x$,
--
--   $$
--   V^{\pi}(x)\le V^{\pi^*}(x).
--   $$
--
--   This is the pointwise policy-dominance form of the Gittins index theorem. It isolates the prevailing-charge and interleaving argument from the order-theoretic final step that identifies the optimal value with the supremum over policies.
--
--   **Formalization Note** Policies may be randomized Markov kernels on the complete observed history. The integrability assumption is the formal version of Assumption 35.6.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), proof of Theorem 35.9, printed pp. 450--453: Part 1 (prevailing charge) and Part 2 (interleaving prevailing charges), using Lemma 35.10.

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_GittinsIndex

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittins_index_policy_dominates
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (πstar : MarkovBanditPolicy k S) (hπ : IsGittinsIndexPolicy P r α πstar)
    (x : Fin k → S) :
    ∀ π : MarkovBanditPolicy k S,
      markovBanditDiscountedValue P r α π x ≤
        markovBanditDiscountedValue P r α πstar x := by
  sorry
