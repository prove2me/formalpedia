-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_centered_product_coordinate_cancellation
-- name    : ZeroFreeRRG.Hardcore.centered_product_coordinate_cancellation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:06:44.850962+00:00
-- url     : https://prove2.me/theorems/f824568d-8980-4013-95ca-f29ad22248fa
-- title:
--   Mean-zero cancellation in product derivative terms
-- statement:
--   Let $X_1,\ldots,X_d$ be independent with a mean-zero integrable law, and let $\varphi$ be any real function. For indices $i,j$, the integral of $$X_j\varphi(X_i)\prod_{k\ne j}(1+\theta X_k)$$ is zero when $i\ne j$, and equals $\mathbb E[X\varphi(X)]$ when $i=j$. The identity uses the Bochner convention even when an integral does not exist in the ordinary sense.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.centered_product_coordinate_cancellation (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (θ : ℝ) (hint : Integrable (fun x : ℝ => x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 0) (φ : ℝ → ℝ) (i j : Fin d) :
    (∫ xs : Fin d → ℝ, ((∏ k ∈ Finset.univ.erase j, (1+θ*xs k))*xs j) * φ (xs i)
      ∂(Measure.pi fun _ : Fin d => μ)) = if i=j then (∫ x, x*φ x ∂μ) else 0 := by sorry
