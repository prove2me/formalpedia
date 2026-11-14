-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_latent_mixture_marginal
-- name    : ZeroFreeRRG.Hardcore.latent_mixture_marginal
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:39:48.481228+00:00
-- url     : https://prove2.me/theorems/3fa733e8-43db-46fb-8ab7-6bd06cd3e255
-- title:
--   Marginalization of a finite latent observation mixture
-- statement:
--   Let $A_i$ be real weights and let each integrable observation density $w_i$ have mean one under $\mu$. For fixed $x$, integrating $\sum_i A_i w_i(x)w_i(y)$ over $y$ gives $\sum_i A_i w_i(x)$. This is the marginal identity for the latent-color mixture used in Lemma 4.27.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.27, printed p. 34.

import Mathlib
open scoped BigOperators
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
theorem latent_mixture_marginal {ι X : Type} [Fintype ι] [MeasurableSpace X] (μ : Measure X)
    (A : ι → ℝ) (w : ι → X → ℝ)
    (hint : ∀ i, Integrable (w i) μ)
    (hmean : ∀ i, (∫ y, w i y ∂μ) = 1) (x : X) :
    (∫ y, ∑ i, A i * w i x * w i y ∂μ) = ∑ i, A i * w i x := by sorry
end ZeroFreeRRG.Hardcore
