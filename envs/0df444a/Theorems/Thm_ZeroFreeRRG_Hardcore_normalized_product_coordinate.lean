-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_normalized_product_coordinate
-- name    : ZeroFreeRRG.Hardcore.normalized_product_coordinate
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:07:23.656545+00:00
-- url     : https://prove2.me/theorems/16a59503-cd00-4e1d-a2e8-8ff61934e256
-- title:
--   A normalized product leaves one coordinate integral
-- statement:
--   If independent variables have common law $\mu$ and $\int a\,d\mu=1$, then for any coordinate $i$ the integral of $\varphi(X_i)\prod_j a(X_j)$ equals $\int a(x)\varphi(x)\,d\mu(x)$. Integrals use the Bochner convention.
-- source:
--   Standard product integration identity; used in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.normalized_product_coordinate (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a φ : ℝ → ℝ) (ha : (∫ x, a x ∂μ) = 1) (i : Fin d) :
    (∫ xs : Fin d → ℝ, (∏ j, a (xs j)) * φ (xs i)
      ∂(Measure.pi fun _ : Fin d => μ)) = ∫ x, a x * φ x ∂μ := by sorry
