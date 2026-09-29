-- Prove2me | Theorems.Thm_BanditAlgorithm_exists_optimal_tracking_policy
-- name    : BanditAlgorithm.exists_optimal_tracking_policy
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T18:37:56.049554+00:00
-- url     : https://prove2.me/theorems/c08eaff1-4473-41e9-8f23-1872a1b2474b
-- title:
--   D-Tracking: a $\\delta$-free policy whose allocation converges to $\\alpha^*(\\nu)$
-- statement:
--   (**D-Tracking**, existence of an optimal tracking sampling rule; L&S Algorithm 21 lines 4–7, Garivier–Kaufmann Lemma 8) There is a single policy $\pi$ — not depending on the confidence level $\delta$ — such that for every unit-variance Gaussian bandit $\nu$ with a unique optimal arm there is an allocation $\alpha\in\mathcal{P}_{k-1}$ attaining the supremum in
--   $$c^*(\nu)^{-1}=\sup_{\alpha}\ \inf_{\nu'\in\mathcal{E}_{\mathrm{alt}}(\nu)}\ \sum_i\alpha_i D(\nu_i,\nu'_i)$$
--   for which, almost surely, the empirical allocation converges to it: $T_i(t)/t\to\alpha_i$ for every arm $i$.
--
--   The witness is the sampling rule of Algorithm 21: at each round, if $\min_i T_i(t)\le\sqrt{t}$ play $\operatorname{argmin}_i T_i(t)$ (forced exploration), and otherwise play $\operatorname{argmax}_i\bigl(t\,\hat\alpha^*_i(t)-T_i(t)\bigr)$, where $\hat\alpha^*(t)=\alpha^*(\hat\nu(t))$ is the optimal allocation of the empirical bandit. The forced-exploration step guarantees every arm is played order $\sqrt{t}$ times, hence $\hat\mu(t)\to\mu(\nu)$; continuity of $\alpha^*$ at $\nu$ (which is where the uniqueness of the optimal arm is used) then gives $\hat\alpha^*(t)\to\alpha^*(\nu)$, and the tracking step converts that into convergence of the realised allocation.
--
--   That the policy does not depend on $\delta$ is essential: L&S Theorem 33.6 asserts a *single* policy together with a family of stopping rules indexed by $\delta$, and this node supplies the policy.
--
--   L&S remark (§33.3 discussion) that the forced-exploration step is rarely useful in practice but genuinely necessary here: without it, when $\mu_2=\mu_3$ the strategy can fail to terminate with positive probability.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Algorithm 21 lines 4-7, p. 410; Garivier & Kaufmann, COLT 2016, Lemma 8 (D-Tracking) with Lemma 19 (forced exploration)

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit


open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.exists_optimal_tracking_policy {k : ℕ} [NeZero k] :
    ∃ π : BanditPolicy k, ∀ ν ∈ Set.range (gaussianBandit (k := k)),
      (∃! i, i ∈ banditOptimalArms ν) →
        ∃ α : Fin k → ℝ≥0,
          IsOptimalAllocation ν (Set.range (gaussianBandit (k := k))) α ∧
            ∀ᵐ ω ∂banditTrajMeasure ν π, ∀ i : Fin k,
              Tendsto (fun t : ℕ ↦ trajAllocation i t ω) atTop (nhds ((α i : ℝ))) := by
  sorry
