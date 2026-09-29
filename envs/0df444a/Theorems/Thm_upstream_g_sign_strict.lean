-- Prove2me | Theorems.Thm_upstream_g_sign_strict
-- name    : upstream_g_sign_strict
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T21:57:33.178913+00:00
-- url     : https://prove2.me/theorems/af6cbf3e-e8ae-4a1d-ba24-f32286ce54fb
-- title:
--   Strict single-crossing sign data for the symmetrized density difference
-- statement:
--   **Single-crossing sign data for the symmetrized-density difference (strict interior crossing).** For a strictly positive density $f$ on $(0,2\mu)$, suppose the log-difference $\varphi(x)=\log f(x)-\log f(2\mu-x)$ has a single interior maximum at $a\in(0,\mu)$ (i.e. $\varphi'>0$ on $(0,a)$ and $\varphi'<0$ on $(a,\mu)$), is continuous on $(0,\mu]$, takes a negative value at some $t_0\in(0,a)$ (true since $\varphi\to-\infty$ as $x\to0^+$), and satisfies the boundary inequality $f(0)\le f(2\mu)$. Then there is a **strictly interior** crossing point $c\in(0,\mu)$ with $g(x)=f(x)-f(2\mu-x)\le 0$ on $[0,c]$ and $g(x)\ge 0$ on $[c,\mu]$. This is the strict-$c$ strengthening of the interior-crossing lemma (the IVT crossing it produces lies in $(t_0,a)\subset(0,\mu)$); the strict $c<\mu$ is required by the mass-flavoured moustache value bound. Source: Siegel, *Median Bounds and their Application*, J. Algorithms 38 (2001), Thm 2.1.

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
open Set

theorem upstream_g_sign_strict
    (f φ' : ℝ → ℝ) (μ a t₀ : ℝ) (hμ : 0 < μ) (ha : a ∈ Ioo (0:ℝ) μ)
    (hfpos : ∀ x ∈ Ioo (0:ℝ) (2*μ), 0 < f x)
    (hφd : ∀ x ∈ Ioo (0:ℝ) μ,
        HasDerivAt (fun y => Real.log (f y) - Real.log (f (2*μ - y))) (φ' x) x)
    (hφpos : ∀ x ∈ Ioo (0:ℝ) a, 0 < φ' x)
    (hφneg : ∀ x ∈ Ioo a μ, φ' x < 0)
    (hφcont : ContinuousOn (fun y => Real.log (f y) - Real.log (f (2*μ - y))) (Ioc 0 μ))
    (ht₀ : t₀ ∈ Ioo (0:ℝ) a) (hφt₀ : Real.log (f t₀) - Real.log (f (2*μ - t₀)) < 0)
    (hg0 : f 0 - f (2*μ) ≤ 0) :
    ∃ c ∈ Ioo (0:ℝ) μ,
      (∀ x ∈ Icc (0:ℝ) c, f x - f (2*μ - x) ≤ 0)
        ∧ (∀ x ∈ Icc c μ, 0 ≤ f x - f (2*μ - x)) := by sorry
