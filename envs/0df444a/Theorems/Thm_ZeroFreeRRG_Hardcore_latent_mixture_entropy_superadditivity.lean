-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_latent_mixture_entropy_superadditivity
-- name    : ZeroFreeRRG.Hardcore.latent_mixture_entropy_superadditivity
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:48:11.505211+00:00
-- url     : https://prove2.me/theorems/454d2beb-67a5-46a4-9ecb-a488cb939fb5
-- title:
--   Entropy inequality for a finite latent observation mixture
-- statement:
--   Let $A_i\ge0$ have positive sum $S$, and let $w_i$ be nonnegative integrable densities of mean one under a probability measure $\mu$. Define $L(x)=\sum_i A_iw_i(x)$ and $T(x,y)=\sum_i A_iw_i(x)w_i(y)$. If $T\log T$, $T\log L(x)$, and $T\log L(y)$ are integrable under $\mu\otimes\mu$, then $$2\int L\log L\,d\mu\le\int T\log T\,d(\mu\otimes\mu)+S\log S.$$ This is the conditional relative-entropy step in the vertex entropy convexity argument.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.27, printed p. 34.

import Mathlib
open scoped BigOperators
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
theorem latent_mixture_entropy_superadditivity {ι X : Type} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (A : ι → ℝ) (w : ι → X → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hS : 0 < ∑ i, A i)
    (hw : ∀ i x, 0 ≤ w i x) (hint : ∀ i, Integrable (w i) μ)
    (hmean : ∀ i, (∫ x, w i x ∂μ) = 1)
    (hTlog : Integrable (fun p : X × X =>
      (∑ i, A i*w i p.1*w i p.2)*Real.log (∑ i, A i*w i p.1*w i p.2)) (μ.prod μ))
    (hcrossL : Integrable (fun p : X × X =>
      (∑ i, A i*w i p.1*w i p.2)*Real.log (∑ i, A i*w i p.1)) (μ.prod μ))
    (hcrossR : Integrable (fun p : X × X =>
      (∑ i, A i*w i p.1*w i p.2)*Real.log (∑ i, A i*w i p.2)) (μ.prod μ)) :
    2*(∫ x, (∑ i, A i*w i x)*Real.log (∑ i, A i*w i x) ∂μ) ≤
      (∫ p : X × X, (∑ i, A i*w i p.1*w i p.2)*Real.log (∑ i, A i*w i p.1*w i p.2) ∂(μ.prod μ)) +
      (∑ i, A i)*Real.log (∑ i, A i) := by sorry
end ZeroFreeRRG.Hardcore
