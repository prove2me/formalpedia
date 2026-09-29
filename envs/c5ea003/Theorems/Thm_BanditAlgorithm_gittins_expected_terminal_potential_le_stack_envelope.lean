-- Prove2me | Theorems.Thm_BanditAlgorithm_gittins_expected_terminal_potential_le_stack_envelope
-- name    : BanditAlgorithm.gittins_expected_terminal_potential_le_stack_envelope
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T17:05:51.567928+00:00
-- url     : https://prove2.me/theorems/d53e04c1-0b22-4d44-aed9-81bbf9f1b9ac
-- title:
--   Expected Gittins terminal-potential envelope
-- statement:
--   For any finite horizon $N$ and any Markov bandit policy $\pi$, the expected terminal Gittins retirement potential is bounded by the expectation of the explicit retirement envelope on the common product space of independent arm trajectories:
--
--   $$
--   U_N^\pi\le \int E_N(\omega)\,dM_x(\omega).
--   $$
--
--   Here $M_x$ is the product of the arms' Markov-chain laws started from the initial state vector $x$. The envelope is displayed explicitly in the formal statement and is independent of the policy.
--
--   This theorem transfers the pathwise retirement-envelope estimate to arbitrary adaptive policies.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, §35.4, proof of Lemma 35.10, printed pp. 452–453 (free PDF pp. 460–461), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_GittinsTerminalPotential

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittins_expected_terminal_potential_le_stack_envelope
    {k N : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    let absoluteValue := fun y : S ↦
      ∫ path, ∑' t : ℕ, α ^ t * |r (path t)|
        ∂markovChainMeasure P y
    let envelope := fun (ω : Fin k → ℕ → S) ↦ ∑ i : Fin k,
      ((∑ u ∈ Finset.range (N + 1), absoluteValue (ω i u)) +
        (∑' t : ℕ, α ^ t) *
          (absoluteValue (ω i 0) +
            ∑ v ∈ Finset.range N, |r (ω i (v + 1))|))
    let stackMeasure : Measure (Fin k → ℕ → S) :=
      Measure.pi (fun i ↦ markovChainMeasure P (x i))
    markovBanditExpectedRetirementPotential P r α π x N ≤
      ∫ ω, envelope ω ∂stackMeasure := by
  sorry
