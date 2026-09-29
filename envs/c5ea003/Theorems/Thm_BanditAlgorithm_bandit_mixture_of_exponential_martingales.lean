-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_mixture_of_exponential_martingales
-- name    : BanditAlgorithm.bandit_mixture_of_exponential_martingales
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T21:33:25.759687+00:00
-- url     : https://prove2.me/theorems/ffca31c7-437a-4f76-a4df-fdcc49715b5f
-- title:
--   A mixture of bandit exponential martingales is a bandit exponential martingale
-- statement:
--   **A mixture of bandit exponential martingales is again one.** Let $\rho$ be a probability density on an index space $(\iota,\nu)$ and let $W^{(i)}$ be, for each $i$, a nonnegative process on histories with unit mass and the one-step martingale property for the trajectory measure $P$. Then the average
--   $$\overline W_n(h)=\int_\iota \rho(i)\,W^{(i)}_n(h)\,d\nu(i)$$
--   is measurable, has unit mass, and satisfies the same one-step martingale property.
--
--   This is the device that makes the exponential martingale usable for an adaptive sampling rule. For a fixed tilt $\lambda$ the weight $e^{\lambda(S_a-T_a\mu_a)-\lambda^2T_a/2}$ is a martingale, but a fixed tilt is of no use when the optimal one depends on the realised pull counts, which are random. Averaging over a prior on $\lambda$ produces a single martingale whose exponent is the self-normalised deviation, and this lemma is what says the averaging preserves the martingale property. The only analytic input is Tonelli's theorem; the martingale property of the mixture is inherited coordinatewise from the family.
-- source:
--   The method of mixtures: Robbins & Siegmund, Boundary crossing probabilities for the Wiener process (1970); de la Pena, Klass & Lai, Ann. Probab. 32 (2004); Kaufmann & Koolen, Mixture martingales revisited, JMLR 22 (2021). This is the step that averaging over the tilt preserves the martingale property.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

theorem BanditAlgorithm.bandit_mixture_of_exponential_martingales {k : ℕ} {ι : Type*}
    [MeasurableSpace ι] (ν : MeasureTheory.Measure ι) [MeasureTheory.SFinite ν]
    (P : MeasureTheory.Measure (ℕ → Fin k × ℝ)) [MeasureTheory.SFinite P]
    (ρ : ι → ENNReal) (hρm : Measurable ρ) (hρ : ∫⁻ i, ρ i ∂ν = 1)
    (W : ι → (n : ℕ) → BanditAlgorithm.BanditHistory k n → ENNReal)
    (hjoint : ∀ n, Measurable fun q : ι × BanditAlgorithm.BanditHistory k n ↦ W q.1 n q.2)
    (hinit : ∀ i, ∫⁻ ω, W i 0 (BanditAlgorithm.banditTrajPrefix k 0 ω) ∂P = 1)
    (hstep : ∀ (i : ι) (n : ℕ) (F : BanditAlgorithm.BanditHistory k n → ENNReal),
      Measurable F →
        ∫⁻ ω, F (BanditAlgorithm.banditTrajPrefix k n ω)
            * W i (n + 1) (BanditAlgorithm.banditTrajPrefix k (n + 1) ω) ∂P
          = ∫⁻ ω, F (BanditAlgorithm.banditTrajPrefix k n ω)
            * W i n (BanditAlgorithm.banditTrajPrefix k n ω) ∂P) :
    (∀ n : ℕ, Measurable fun hst : BanditAlgorithm.BanditHistory k n ↦ ∫⁻ i, ρ i * W i n hst ∂ν)
      ∧ (∫⁻ ω, (∫⁻ i, ρ i * W i 0 (BanditAlgorithm.banditTrajPrefix k 0 ω) ∂ν) ∂P = 1)
      ∧ ∀ (n : ℕ) (F : BanditAlgorithm.BanditHistory k n → ENNReal), Measurable F →
          ∫⁻ ω, F (BanditAlgorithm.banditTrajPrefix k n ω)
              * (∫⁻ i, ρ i * W i (n + 1)
                  (BanditAlgorithm.banditTrajPrefix k (n + 1) ω) ∂ν) ∂P
            = ∫⁻ ω, F (BanditAlgorithm.banditTrajPrefix k n ω)
              * (∫⁻ i, ρ i * W i n (BanditAlgorithm.banditTrajPrefix k n ω) ∂ν) ∂P := by
  sorry
