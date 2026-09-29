-- Prove2me | Theorems.Thm_siegel_cdf_average_ge_mean
-- name    : siegel_cdf_average_ge_mean
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T15:42:05.964951+00:00
-- url     : https://prove2.me/theorems/df8aa8f6-116f-4c3a-be87-1baf2439dbab
-- title:
--   Siegel Lemma 2.1: the averaged CDF at the mean is at least $\tfrac12$
-- statement:
--   **Siegel 2001, Lemma 2.1** (Median Bounds and their Application, J. Algorithms 38:184-236, p.4-5). Let $X$ be a nonnegative random variable with cumulative distribution function $F$ (so $F(0)=0$, $F'=f$ the density, $f\ge 0$) and finite mean $\mu = \int_0^\infty t\,f(t)\,dt$, with total mass $\int_0^\infty f(t)\,dt = 1$. Then the average value of the CDF over $[0,2\mu]$ is at least $\mu$: $$\int_0^{2\mu} F(t)\,dt = \mu + \int_{2\mu}^\infty (t-2\mu)\,f(t)\,dt \ge \mu.$$ The improper facts (total mass $1$ and mean $\mu$) are taken as hypotheses (standard probabilistic packaging). This is the reusable real-analysis core of Siegel's median machinery, used to prove the moustache-CDF value bound (Theorem 2.1) and thence the integer-mean binomial/Bernoulli median (Theorem 2.2 = Jogdeo-Samuels).
-- source:
--   Siegel, A. (2001). Median Bounds and their Application. Journal of Algorithms 38(1):184-236, Lemma 2.1, p.4-5. Proof = single integration by parts of the CDF against (t-2mu).

import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

theorem siegel_cdf_average_ge_mean (μ : ℝ) (hμ : 0 ≤ μ) (F f : ℝ → ℝ) (hF : ∀ x ∈ Set.Ici (0:ℝ), HasDerivAt F (f x) x) (hfnn : ∀ x ∈ Set.Ici (0:ℝ), 0 ≤ f x) (hF0 : F 0 = 0) (hf_int_loc : ∀ b : ℝ, IntervalIntegrable f MeasureTheory.volume 0 b) (hf_mass : MeasureTheory.IntegrableOn f (Set.Ioi (0:ℝ))) (htf_mass : MeasureTheory.IntegrableOn (fun t => t * f t) (Set.Ioi (0:ℝ))) (hmass : ∫ t in Set.Ioi (0:ℝ), f t = 1) (hmean : ∫ t in Set.Ioi (0:ℝ), t * f t = μ) : μ ≤ ∫ t in (0:ℝ)..(2*μ), F t := by sorry
