-- Prove2me | Theorems.Thm_siegel_moustache_value_bound
-- name    : siegel_moustache_value_bound
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T17:43:47.251729+00:00
-- url     : https://prove2.me/theorems/8bc80e19-9c4c-4c92-b3c6-0c8206d19661
-- title:
--   Siegel Theorem 2.1: the “moustache” value bound
-- statement:
--   Siegel 2001, Theorem 2.1 (the "moustache" value bound), geometric core. Let $G:\mathbb{R}\to\mathbb{R}$ on $[0,2\mu]$ ($\mu>0$) be symmetric about $\mu$ ($G(2\mu-x)=G(x)$), valley-shaped on $[0,\mu]$ (antitone on $[0,c]$ then monotone on $[c,\mu]$, i.e. a single interior minimum), with $G(0)\le G(\mu)$. If the average of $G$ over $[0,2\mu]$ is at least $1/2$ (which Siegel's Lemma 2.1 supplies for a symmetrized CDF), then $G(\mu)\ge 1/2$. This is the ordering-analysis step in Siegel's proof of the integer-mean binomial/Poisson median bound (Thm 2.2).
-- source:
--   A. Siegel, "Median Bounds and their Application", Journal of Algorithms 38 (2001) 184-236, Theorem 2.1, p.5 (the moustache-CDF value bound). Geometric core abstracted as pure real analysis; the average>=1/2 hypothesis is supplied by Siegel Lemma 2.1 (already proved on platform as siegel_cdf_average_ge_mean).

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Monotone.Basic

set_option autoImplicit false

open MeasureTheory

theorem siegel_moustache_value_bound
    (G : ℝ → ℝ) (μ c : ℝ) (hμ : 0 < μ) (hc0 : 0 ≤ c) (hcμ : c ≤ μ)
    (hleft : AntitoneOn G (Set.Icc 0 c))
    (hright : MonotoneOn G (Set.Icc c μ))
    (hsym : ∀ x, G (2 * μ - x) = G x)
    (h0μ : G 0 ≤ G μ)
    (hint : IntervalIntegrable G volume 0 (2 * μ))
    (havg : (1 / 2 : ℝ) ≤ (1 / (2 * μ)) * ∫ x in (0:ℝ)..(2 * μ), G x) :
    (1 / 2 : ℝ) ≤ G μ := by sorry
