-- Prove2me | Theorems.Thm_siegel_symmetrized_cdf_unimodal_from_density_sign
-- name    : siegel_symmetrized_cdf_unimodal_from_density_sign
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T18:09:48.007255+00:00
-- url     : https://prove2.me/theorems/277f4166-6892-4c0b-a947-5999c108af21
-- title:
--   Siegel Theorem 2.1: unimodality of the symmetrized CDF
-- statement:
--   **Siegel 2001, Theorem 2.1 — the derivative-test (monotonicity) half.**
--
--   Let $F$ be a cumulative distribution function with density $f$, i.e. $F'=f$ everywhere, and let
--   $$\hat F(x)=\frac{F(x)+F(2\mu-x)}{2}$$
--   be its symmetrization about $\mu$. By the chain rule $\hat F'(x)=\frac{f(x)-f(2\mu-x)}{2}$, so the sign of $g(x):=f(x)-f(2\mu-x)$ governs the monotonicity of $\hat F$.
--
--   If there is a single interior turning point $c\in[0,\mu]$ with $g\le 0$ on $[0,c]$ and $g\ge 0$ on $[c,\mu]$ (the "single interior minimum"/moustache shape, Siegel's condition 2), then $\hat F$ is antitone on $[0,c]$ and monotone on $[c,\mu]$.
--
--   This supplies exactly the two order hypotheses (`hleft`, `hright`) consumed by `siegel_moustache_value_bound`, turning raw density sign-data into the moustache shape.
-- source:
--   Siegel, A. (2001). "Median Bounds and their Application." Journal of Algorithms 38(1):184-236. Theorem 2.1, p.5: in the proof, F̂ is decreasing at the origin (since f(0)<f(2µ)) and its single interior zero of F̂'=(f(x)-f(2µ-x))/2 is a minimum, after which F̂ increases. This node formalizes the derivative-sign ⟹ monotonicity step (antitone-then-monotone). Mathlib lemmas: antitoneOn_of_hasDerivWithinAt_nonpos, monotoneOn_of_hasDerivWithinAt_nonneg.

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
set_option autoImplicit false

theorem siegel_symmetrized_cdf_unimodal_from_density_sign (F f : ℝ → ℝ) (μ c : ℝ) (hF : ∀ x, HasDerivAt F (f x) x) (hgL : ∀ x ∈ Set.Icc (0:ℝ) c, f x - f (2 * μ - x) ≤ 0) (hgR : ∀ x ∈ Set.Icc c μ, 0 ≤ f x - f (2 * μ - x)) : AntitoneOn (fun x => (F x + F (2 * μ - x)) / 2) (Set.Icc 0 c) ∧ MonotoneOn (fun x => (F x + F (2 * μ - x)) / 2) (Set.Icc c μ) := by sorry
