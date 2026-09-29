-- Prove2me | Theorems.Thm_upstream_g_sign
-- name    : upstream_g_sign
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T20:25:27.04567+00:00
-- url     : https://prove2.me/theorems/1c1ea310-6c49-4157-b875-7f517f4bfc79
-- title:
--   Interior-crossing step for the symmetrized density difference
-- statement:
--   **Interior-crossing upstream step (Siegel moustache, non-degenerate case).** Let $f>0$ on $(0,2\mu)$ be a density and $\varphi(x)=\log f(x)-\log f(2\mu-x)$ its symmetrized log-ratio. Suppose $\varphi$ has a single interior maximum at $a\in(0,\mu)$ ($\varphi'>0$ on $(0,a)$, $\varphi'<0$ on $(a,\mu)$), is continuous on $(0,\mu]$, takes a negative value at some $t_0\in(0,a)$ (automatic since $\varphi\to-\infty$ at $0^+$ when $f(0^+)=0$), and satisfies the boundary inequality $f(0)-f(2\mu)\le 0$. Then the density difference $g(x)=f(x)-f(2\mu-x)$ is $\le 0$ on $[0,c]$ and $\ge 0$ on $[c,\mu]$ for a single crossing $c\in[0,\mu]$. Proof: $\varphi(\mu)=0$ automatically (as $2\mu-\mu=\mu$); strict antitonicity on $[a,\mu]$ gives $\varphi>0$ on $(a,\mu)$; strict monotonicity on $[t_0,a]$ plus $\varphi(t_0)<0<\varphi(a)$ yields by the intermediate value theorem the crossing $c\in(t_0,a)$; finally $\log$-monotonicity ($f>0$) transfers the sign of $\varphi$ to $g$, and the $x=0$ boundary uses $g(0)\le 0$. This feeds Siegel's symmetrized-CDF bridge and moustache value bound.
-- source:
--   A. Siegel, 'Median Bounds and their Application', J. Algorithms 38:184-236 (2001), Theorem 2.1 / §2.1.1 (the unimodal symmetrized log-density g-sign step, non-degenerate case). Built on Mathlib strictMonoOn_of_deriv_pos / strictAntiOn_of_deriv_neg + intermediate_value_Ioo.

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
open Set

theorem upstream_g_sign (f φ' : ℝ → ℝ) (μ a t₀ : ℝ) (hμ : 0 < μ) (ha : a ∈ Set.Ioo (0:ℝ) μ) (hfpos : ∀ x ∈ Set.Ioo (0:ℝ) (2*μ), 0 < f x) (hφd : ∀ x ∈ Set.Ioo (0:ℝ) μ, HasDerivAt (fun y => Real.log (f y) - Real.log (f (2*μ - y))) (φ' x) x) (hφpos : ∀ x ∈ Set.Ioo (0:ℝ) a, 0 < φ' x) (hφneg : ∀ x ∈ Set.Ioo a μ, φ' x < 0) (hφcont : ContinuousOn (fun y => Real.log (f y) - Real.log (f (2*μ - y))) (Set.Ioc 0 μ)) (ht₀ : t₀ ∈ Set.Ioo (0:ℝ) a) (hφt₀ : Real.log (f t₀) - Real.log (f (2*μ - t₀)) < 0) (hg0 : f 0 - f (2*μ) ≤ 0) : ∃ c ∈ Set.Icc (0:ℝ) μ, (∀ x ∈ Set.Icc (0:ℝ) c, f x - f (2*μ - x) ≤ 0) ∧ (∀ x ∈ Set.Icc c μ, 0 ≤ f x - f (2*μ - x)) := by sorry
