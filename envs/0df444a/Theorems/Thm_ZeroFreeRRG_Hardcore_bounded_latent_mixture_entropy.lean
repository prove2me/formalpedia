-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_bounded_latent_mixture_entropy
-- name    : ZeroFreeRRG.Hardcore.bounded_latent_mixture_entropy
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:50:36.216931+00:00
-- url     : https://prove2.me/theorems/ef213add-ed1d-4473-aeed-2478a1cf27fe
-- title:
--   Entropy superadditivity for bounded latent mixtures
-- statement:
--   Let $A_i\ge0$ have positive sum $S$, and let bounded measurable densities $0\le w_i\le C$ each have mean one under a probability measure $\mu$. Put $L(x)=\sum_i A_iw_i(x)$ and $T(x,y)=\sum_i A_iw_i(x)w_i(y)$. Then $$2\int L\log L\,d\mu\le\int T\log T\,d(\mu\otimes\mu)+S\log S.$$ Boundedness supplies the logarithmic integrability, including at zero. This is the conditional entropy inequality used in Lemma 4.27.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.27, printed p. 34.

import Mathlib
open scoped BigOperators
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
theorem bounded_latent_mixture_entropy {ι X : Type} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (A : ι → ℝ) (w : ι → X → ℝ) (C : ℝ)
    (hA : ∀ i, 0 ≤ A i) (hS : 0 < ∑ i, A i) (hC : 0 ≤ C)
    (hw : ∀ i x, 0 ≤ w i x ∧ w i x ≤ C) (hwm : ∀ i, Measurable (w i))
    (hmean : ∀ i, (∫ x, w i x ∂μ) = 1) :
    2*(∫ x, (∑ i, A i*w i x)*Real.log (∑ i, A i*w i x) ∂μ) ≤
      (∫ p : X × X, (∑ i, A i*w i p.1*w i p.2)*Real.log (∑ i, A i*w i p.1*w i p.2) ∂(μ.prod μ)) +
      (∑ i, A i)*Real.log (∑ i, A i) := by sorry
end ZeroFreeRRG.Hardcore
