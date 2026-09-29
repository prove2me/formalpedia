-- Prove2me | Theorems.Thm_unimodal_single_crossing
-- name    : unimodal_single_crossing
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T18:20:08.842917+00:00
-- url     : https://prove2.me/theorems/0ec5882f-fb48-4e31-9958-3bf462654ebe
-- title:
--   Single-crossing lemma for a unimodal function
-- statement:
--   **Single-crossing lemma for a unimodal companion function (Siegel 2001, Theorem 2.1, p.5, the IVT step).** If $g:\mathbb R\to\mathbb R$ is continuous on $[0,\mu]$, strictly increasing on $[0,a]$ and strictly decreasing on $[a,\mu]$ (a single interior maximum, $0<a<\mu$), with $g(0)<0$ and $g(\mu)=0$, then there is a single crossing point $c\in(0,a)$ with $g\le 0$ on $[0,c]$ and $g\ge 0$ on $[c,\mu]$. This is the ordering/IVT step that turns the unimodality of the (log-)density-difference $g(x)=\log f(x)-\log f(2\mu-x)$ into the sign data $g\le0$ on $[0,c]$, $g\ge0$ on $[c,\mu]$ consumed by Siegel's symmetrized-CDF monotonicity step (`siegel_symmetrized_cdf_unimodal_from_density_sign`).
-- source:
--   A. Siegel, "Median Bounds and their Application", J. Algorithms 38:184-236, 2001, Theorem 2.1, p.5 (the single-interior-minimum / intermediate-value step). Standard intermediate-value-theorem + monotonicity argument.

import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit false
open Set

theorem unimodal_single_crossing
    (g : ℝ → ℝ) (μ a : ℝ)
    (ha0 : 0 < a) (haμ : a < μ)
    (hcont : ContinuousOn g (Icc 0 μ))
    (hinc : StrictMonoOn g (Icc 0 a))
    (hdec : StrictAntiOn g (Icc a μ))
    (hg0 : g 0 < 0)
    (hgμ : g μ = 0) :
    ∃ c, 0 < c ∧ c < a ∧
      (∀ x ∈ Icc (0:ℝ) c, g x ≤ 0) ∧ (∀ x ∈ Icc c μ, 0 ≤ g x) := by sorry
