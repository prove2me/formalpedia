-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_comonotone_covariance_nonnegative
-- name    : ZeroFreeRRG.Hardcore.comonotone_covariance_nonnegative
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:05:08.020767+00:00
-- url     : https://prove2.me/theorems/00e9c730-9da8-4c65-b18a-c9cfd4ef5876
-- title:
--   Nonnegative covariance of comonotone variables
-- statement:
--   Let $f$ and $g$ be integrable real random variables on a probability space, with integrable product. If $(f(x)-f(y))(g(x)-g(y))\ge0$ for all $x,y$, then $\mathbb E[f]\mathbb E[g]\le\mathbb E[fg]$. This supplies the basic size-bias ordering inequality for the hardcore Bethe monotonicity argument.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 30.

import Mathlib
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
theorem comonotone_covariance_nonnegative {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x => f x*g x) μ)
    (hmono : ∀ x y, 0 ≤ (f x-f y)*(g x-g y)) :
    (∫ x, f x ∂μ)*(∫ x, g x ∂μ) ≤ ∫ x, f x*g x ∂μ := by sorry
end ZeroFreeRRG.Hardcore
