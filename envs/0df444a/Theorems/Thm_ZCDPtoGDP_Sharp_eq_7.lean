-- Prove2me | Theorems.Thm_ZCDPtoGDP_Sharp_eq_7
-- name    : ZCDPtoGDP.Sharp.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:55:48.745202+00:00
-- url     : https://prove2.me/theorems/7fcf8097-054d-486d-8d30-822750ea009f
-- title:
--   §B.1.1, eq. (7) — Rényi data processing for the binary decision
-- statement:
--   Let $P,Q$ be probability measures on a measurable space $\Omega$ and let $\phi:\Omega\to[0,1]$ be a measurable test with $p=\mathbb E_P\phi$ and $q=\mathbb E_Q\phi$. The binary decision $B\mid\omega\sim\mathrm{Bern}(\phi(\omega))$ has law $\mathrm{Bern}(p)$ under $P$ and $\mathrm{Bern}(q)$ under $Q$. For every order $\eta>1$,
--   $$D_\eta(\mathrm{Bern}(p)\|\mathrm{Bern}(q))\le D_\eta(P\|Q),\qquad D_\eta(\mathrm{Bern}(q)\|\mathrm{Bern}(p))\le D_\eta(Q\|P).$$
--
--   This is the data-processing inequality for Rényi divergence applied to the post-processing $\omega\mapsto B$; it transfers a zCDP violation of the Bernoulli pair back to the mechanism's output pair. Both divergences may equal $+\infty$.
--
--   Differences from the source:
--   - encoding: P = M(x), Q = M(x′) for neighbouring x ∼ x′ → arbitrary probability measures P, Q on Ω; reason: every such pair is the output pair of the two-input mechanism x ↦ P, x′ ↦ Q, so the instances coincide
-- source:
--   Chen, Pandey, Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf, §B.1.1, eq. (7), p. 14

import Mathlib
import Definitions.Def_ZCDPtoGDP_Sharp_Privacy
import Definitions.Def_ZCDPtoGDP_Sharp_Analysis

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ZCDPtoGDP.Sharp

/-- §B.1.1, eq. (7), p. 14: Rényi data processing for the binary decision
`B | ω ∼ Bern(φ ω)`, whose laws under `P` and `Q` are `Bern(E_P φ)` and `Bern(E_Q φ)`. -/
theorem eq_7 {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : Ω → ℝ) (hφ : IsTest φ)
    (η : ℝ) (hη : 1 < η) :
    renyiDiv η (bern (∫ ω, φ ω ∂P)) (bern (∫ ω, φ ω ∂Q)) ≤ renyiDiv η P Q ∧
    renyiDiv η (bern (∫ ω, φ ω ∂Q)) (bern (∫ ω, φ ω ∂P)) ≤ renyiDiv η Q P := by sorry

end ZCDPtoGDP.Sharp
