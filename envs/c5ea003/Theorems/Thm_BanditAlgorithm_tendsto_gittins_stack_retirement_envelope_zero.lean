-- Prove2me | Theorems.Thm_BanditAlgorithm_tendsto_gittins_stack_retirement_envelope_zero
-- name    : BanditAlgorithm.tendsto_gittins_stack_retirement_envelope_zero
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T17:06:10.568698+00:00
-- url     : https://prove2.me/theorems/623ab10e-42b7-4090-ba4c-ba8eb4781119
-- title:
--   Vanishing discounted Gittins retirement envelope
-- statement:
--   Let $E_N$ be the explicit retirement envelope on the common product space of independent arm trajectories. Under discounted absolute-reward integrability and $0<\alpha<1$, its discounted expectation vanishes:
--
--   $$
--   \alpha^N\int E_N(\omega)\,dM_x(\omega)\longrightarrow0.
--   $$
--
--   The envelope contains finite prefixes of absolute discounted-reward values and absolute one-step rewards. This tail statement is the uniform-integrability limit needed to pass from the finite prevailing-charge comparison to the infinite-horizon Gittins theorem.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, §35.4, proof of Lemma 35.10 and passage to the limit, printed pp. 452–453 (free PDF pp. 460–461), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_GittinsTerminalPotential

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.tendsto_gittins_stack_retirement_envelope_zero
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : Fin k → S) :
    let absoluteValue := fun y : S ↦
      ∫ path, ∑' t : ℕ, α ^ t * |r (path t)|
        ∂markovChainMeasure P y
    let envelope := fun (N : ℕ) (ω : Fin k → ℕ → S) ↦ ∑ i : Fin k,
      ((∑ u ∈ Finset.range (N + 1), absoluteValue (ω i u)) +
        (∑' t : ℕ, α ^ t) *
          (absoluteValue (ω i 0) +
            ∑ v ∈ Finset.range N, |r (ω i (v + 1))|))
    let stackMeasure : Measure (Fin k → ℕ → S) :=
      Measure.pi (fun i ↦ markovChainMeasure P (x i))
    Filter.Tendsto (fun N ↦ α ^ N * ∫ ω, envelope N ω ∂stackMeasure)
      Filter.atTop (nhds 0) := by
  sorry
