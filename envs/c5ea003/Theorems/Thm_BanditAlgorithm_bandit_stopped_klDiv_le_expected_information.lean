-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_stopped_klDiv_le_expected_information
-- name    : BanditAlgorithm.bandit_stopped_klDiv_le_expected_information
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T19:33:58.301557+00:00
-- url     : https://prove2.me/theorems/59265fba-97de-4354-9eb6-787eb526fe62
-- title:
--   KL divergence decomposition for a stopped adaptive bandit experiment
-- statement:
--   Run an adaptive policy $\pi$ in environments $\nu$ and $\nu'$, and let $\mathcal F_\tau$ be the sigma-algebra observable at an integrable stopping time $\tau$. The KL divergence between the two trajectory laws restricted to $\mathcal F_\tau$ is at most the expected armwise information accumulated before stopping:
--
--   $$
--   D\!\left(\mathbb P_{\nu,\pi}|_{\mathcal F_\tau}\,\middle\Vert\,\mathbb P_{\nu',\pi}|_{\mathcal F_\tau}\right)
--   \le
--   \sum_{i=1}^k \mathbb E_{\nu,\pi}[T_i(\tau)]D(\nu_i\Vert\nu_i').
--   $$
--
--   For the canonical bandit experiment this is in fact an equality under the usual finite-divergence hypotheses; the inequality is the singularity-safe form needed by lower-bound arguments.
-- source:
--   Lattimore--Szepesvári, Bandit Algorithms (CUP 2020), Exercise 15.7, printed p. 211: stopping-time extension of the divergence decomposition in Lemma 15.1, Eq. (15.1), printed p. 198.

import Definitions.Def_BanditTrajectory

open MeasureTheory ProbabilityTheory InformationTheory ENNReal

theorem BanditAlgorithm.bandit_stopped_klDiv_le_expected_information
    {k : ℕ} (ν ν' : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ)
    (hfinite : ∫⁻ ω, (τ ω : ℝ≥0∞) ∂banditTrajMeasure ν π < ⊤) :
    @klDiv (ℕ → Fin k × ℝ) hτ.measurableSpace
        ((banditTrajMeasure ν π).trim hτ.measurableSpace_le)
        ((banditTrajMeasure ν' π).trim hτ.measurableSpace_le) ≤
      ∑ i, (∫⁻ ω, ∑' t : ℕ,
          if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0
        ∂banditTrajMeasure ν π) * klDiv (ν.P i) (ν'.P i) := by
  sorry
