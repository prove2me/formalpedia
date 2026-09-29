-- Prove2me | Theorems.Thm_BanditAlgorithm_gittins_epsilon_optimal_stopping
-- name    : BanditAlgorithm.gittins_epsilon_optimal_stopping
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T03:01:16.928219+00:00
-- url     : https://prove2.me/theorems/283b9493-0156-4e6a-85ed-a4d23831edaa
-- title:
--   Existence of epsilon-optimal stopping times for the Gittins index
-- statement:
--   Let $(S_t)_{t\ge0}$ be a Markov chain with transition kernel $P$, initial state $x$, measurable reward $r:S\to\mathbb R$, and discount factor $\alpha\in(0,1)$. Assume the infinite discounted sum of absolute rewards has finite expectation. For every $\varepsilon>0$, there is an admissible stopping time $\tau\ge1$ whose discounted reward ratio is within $\varepsilon$ of the Gittins index from below:
--
--   $$
--   g(x)-\varepsilon
--   <
--   \frac{\mathbb E_x\!\left[\sum_{t<\tau}\alpha^t r(S_t)\right]}{\mathbb E_x\!\left[\sum_{t<\tau}\alpha^t\right]}.
--   $$
--
--   This epsilon-optimal form is the robust supremum-attainment principle needed to approximate the optimal stopping blocks in prevailing-charge proofs.
--
--   **Formalization Note** The theorem uses strict approximation rather than asserting that the supremum is exactly attained; this follows directly from the conditional supremum after proving nonemptiness and boundedness.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), §35.4.1, printed pp.448--449, Eq. (35.9) and the discussion immediately preceding Lemma 35.7(c).

import Theorems.Thm_BanditAlgorithm_gittins_stopping_ratio_le_index

open MeasureTheory ProbabilityTheory ENNReal
open BanditAlgorithm

theorem BanditAlgorithm.gittins_epsilon_optimal_stopping
    {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α) (x : S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : (ℕ → S) → ℕ∞,
      IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      gittinsIndex P r α x - ε <
        (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P x) /
          (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω
            ∂markovChainMeasure P x) := by
  sorry
