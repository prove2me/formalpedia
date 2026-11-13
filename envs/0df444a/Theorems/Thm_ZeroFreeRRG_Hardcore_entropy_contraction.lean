-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_entropy_contraction
-- name    : ZeroFreeRRG.Hardcore.entropy_contraction
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:30:27.436497+00:00
-- url     : https://prove2.me/theorems/c71ae5d6-d1fc-4fbf-b2c5-940c49801537
-- title:
--   Strict entropy contraction under affine mixing
-- statement:
--   Let $E$ be a nonnegative almost-everywhere real function on a measure space, let $0<c<1$, and suppose both $E\log E$ and $(1-c+cE)\log(1-c+cE)$ are integrable. Then
--
--   $$\int (1-c+cE)\log(1-c+cE)\,d\mu\le c\int E\log E\,d\mu.$$
--
--   The inequality is strict if the set where $E\ge0$ and $E\ne1$ has positive measure. This is the integrated strict-convexity step in the Potts comparison leading to equation (27).
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, equation (27), printed pp. 30–31; generalized integrated convexity step.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
/-- Integrated strict-convexity comparison used for the Potts edge factor. -/
theorem entropy_contraction {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (E : Ω → ℝ)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hE : ∀ᵐ ω ∂μ, 0 ≤ E ω)
    (hI : Integrable (fun ω => xlogx (E ω)) μ)
    (hJ : Integrable (fun ω => xlogx (1-c+c*E ω)) μ) :
    (∫ ω, xlogx (1-c+c*E ω) ∂μ) ≤ c * ∫ ω, xlogx (E ω) ∂μ ∧
      (0 < μ {ω | 0 ≤ E ω ∧ E ω ≠ 1} →
        (∫ ω, xlogx (1-c+c*E ω) ∂μ) < c * ∫ ω, xlogx (E ω) ∂μ) := by sorry
end ZeroFreeRRG.Hardcore
