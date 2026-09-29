-- Prove2me | Theorems.Thm_moustache_value_bound_mass
-- name    : moustache_value_bound_mass
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T21:03:46.18417+00:00
-- url     : https://prove2.me/theorems/3fbb354c-469f-44eb-b1bb-eb549d9860e4
-- title:
--   Siegel's “moustache” value bound, mass-flavoured variant
-- statement:
--   Siegel's "moustache" value bound (median bound), mass-flavoured variant. Let $G:\mathbb R\to\mathbb R$ be a function on $[0,2\mu]$ ($\mu>0$) that is symmetric about $\mu$ ($G(2\mu-x)=G(x)$) and **valley-shaped** on $[0,\mu]$: antitone on $[0,c]$ then monotone on $[c,\mu]$, with the valley minimum strictly interior ($0\le c<\mu$). If the left-endpoint value satisfies $G(0)\le \tfrac12$ and the average of $G$ over $[0,2\mu]$ is at least $\tfrac12$, then the centre value satisfies $G(\mu)\ge\tfrac12$. This is the geometric core of Siegel's integer-mean median bound. Unlike the original `siegel_moustache_value_bound`, this variant takes the hypothesis $G(0)\le\tfrac12$ (which for a symmetrized CDF $G=(F(x)+F(2\mu-x))/2$ is automatic, since $G(0)=F(2\mu)/2\le\tfrac12$ by the mass bound $F\le 1$) in place of $G(0)\le G(\mu)$ (which would be circular with the conclusion).
-- source:
--   A. Siegel, "Median Bounds and their Application", Journal of Algorithms 38(1):184-236, 2001, Theorem 2.1 (the moustache value bound), p.5. Mass-flavoured restatement (G(0)≤1/2 hypothesis).

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Monotone.Basic
open MeasureTheory

theorem moustache_value_bound_mass (G : ℝ → ℝ) (μ c : ℝ) (hμ : 0 < μ) (hc0 : 0 ≤ c) (hcμ : c < μ) (hleft : AntitoneOn G (Set.Icc 0 c)) (hright : MonotoneOn G (Set.Icc c μ)) (hsym : ∀ x, G (2 * μ - x) = G x) (hG0 : G 0 ≤ (1/2 : ℝ)) (hint : IntervalIntegrable G volume 0 (2 * μ)) (havg : (1 / 2 : ℝ) ≤ (1 / (2 * μ)) * ∫ x in (0:ℝ)..(2 * μ), G x) : (1 / 2 : ℝ) ≤ G μ := by sorry
