-- Prove2me | Theorems.Thm_ZCDPtoGDP_Sharp_eq_6
-- name    : ZCDPtoGDP.Sharp.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:56:33.722635+00:00
-- url     : https://prove2.me/theorems/fcd6aec7-2b63-43bb-bad2-4b3e6c305f15
-- title:
--   §B.1, eq. (6) — a GDP violation yields a test with $q>\Phi(\Phi^{-1}(p)+\mu)$
-- statement:
--   Let $P,Q$ be probability measures on a measurable space $\Omega$, let $\mu>0$ and $\alpha\in[0,1]$, and suppose that the trade-off function violates the Gaussian curve at $\alpha$: $T(P,Q)(\alpha)<G_\mu(\alpha)$. Then:
--
--   1. for every $\beta\in(0,1)$, $1-G_\mu(\beta)=\Phi(\Phi^{-1}(\beta)+\mu)$;
--   2. there is a test $\phi:\Omega\to[0,1]$ with type I error $p=\mathbb E_P\phi$ and power $q=\mathbb E_Q\phi$ such that $p\le\alpha$, $1-q<G_\mu(\alpha)$ and
--   $$q>1-G_\mu(\alpha)\ \ge\ 1-G_\mu(p).$$
--
--   With the conventions $\Phi^{-1}(0)=-\infty$, $\Phi^{-1}(1)=+\infty$, the last display is the paper's (6), $q>\Phi(\Phi^{-1}(\alpha)+\mu)\ge\Phi(\Phi^{-1}(p)+\mu)$, including $p=0$. This is the first step of the proof of the conversion: a failure of $\mu$-GDP produces a single test, hence a Bernoulli pair, that is better separated than the Gaussian pair.
--
--   Differences from the source:
--   - encoding: P = M(x), Q = M(x′) for neighbouring x ∼ x′ → arbitrary probability measures P, Q on Ω; reason: every such pair is the output pair of the two-input mechanism x ↦ P, x′ ↦ Q, so the instances coincide
--   - encoding: Φ(Φ⁻¹(α) + μ) and Φ(Φ⁻¹(p) + μ) with Φ⁻¹(0) = −∞, Φ⁻¹(1) = +∞ → 1 − G_μ(α) and 1 − G_μ(p), with G_μ(0) = 1, G_μ(1) = 0, plus the identity 1 − G_μ(β) = Φ(Φ⁻¹(β) + μ) on (0,1); reason: this is the source's identity together with its endpoint conventions, so every value is the same
-- source:
--   Chen, Pandey, Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf, §B.1, eq. (6), p. 13

import Mathlib
import Definitions.Def_ZCDPtoGDP_Sharp_Privacy
import Definitions.Def_ZCDPtoGDP_Sharp_Analysis

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ZCDPtoGDP.Sharp

/-- §B.1, eq. (6), p. 13: a violation of `μ`-GDP at level `α` yields a test `φ` with
`p = E_P φ ≤ α`, `1 - q = 1 - E_Q φ < G_μ(α)` and `q > 1 - G_μ(p)`, where
`1 - G_μ(β) = Φ(Φ⁻¹(β) + μ)` for `β ∈ (0,1)` (endpoint conventions built into `G_μ`). -/
theorem eq_6 {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (μ α : ℝ) (hμ : 0 < μ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hviol : tradeOff P Q α < gaussTradeOff μ α) :
    (∀ β : ℝ, 0 < β → β < 1 →
      1 - gaussTradeOff μ β = stdNormalCDF (stdNormalQuantile β + μ)) ∧
    ∃ φ : Ω → ℝ, IsTest φ ∧ ∫ ω, φ ω ∂P ≤ α ∧ 1 - ∫ ω, φ ω ∂Q < gaussTradeOff μ α ∧
      1 - gaussTradeOff μ α < ∫ ω, φ ω ∂Q ∧
      1 - gaussTradeOff μ (∫ ω, φ ω ∂P) ≤ 1 - gaussTradeOff μ α := by sorry

end ZCDPtoGDP.Sharp
