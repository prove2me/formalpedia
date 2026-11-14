-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_tilted_product_expectation
-- name    : ZeroFreeRRG.Hardcore.tilted_product_expectation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:00:21.257242+00:00
-- url     : https://prove2.me/theorems/535c3593-35d9-4f74-b4be-6e41c778150b
-- title:
--   Expectation of independent transformed tilted samples
-- statement:
--   Let $\mu$ be a probability law, $f$ a nonnegative integrable density whose tilt $f\,d\mu$ is a probability law, and $W$ a measurable map. The expectation of any measurable test $K$ on $d$ independent samples from the image of the tilted law equals the expectation under $\mu^{\otimes d}$ of $$\left(\prod_i f(X_i)\right)K(W(X_1),\ldots,W(X_d)).$$ The identity uses Lean’s convention for nonintegrable Bochner integrals.
-- source:
--   Standard finite-product change of measure; used in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Classical BigOperators ENNReal

theorem ZeroFreeRRG.Hardcore.tilted_product_expectation (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f W : ℝ → ℝ) (hf : Measurable f) (hW : Measurable W)
    (hpos : ∀ x, 0 ≤ f x) (hint : Integrable f μ)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))]
    (K : (Fin d → ℝ) → ℝ) (hK : Measurable K) :
    let ν := Measure.map W (μ.withDensity (fun x => ENNReal.ofReal (f x)))
    (∫ xs : Fin d → ℝ, K xs ∂(Measure.pi fun _ : Fin d => ν)) =
    ∫ xs : Fin d → ℝ, (∏ i, f (xs i)) * K (fun i => W (xs i))
      ∂(Measure.pi fun _ : Fin d => μ) := by sorry
