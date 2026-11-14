-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_finite_product_density
-- name    : ZeroFreeRRG.Hardcore.finite_product_density
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:52:09.685754+00:00
-- url     : https://prove2.me/theorems/0c26fce4-3d19-4699-8d66-a3f854d66bd3
-- title:
--   Finite product of measures with densities
-- statement:
--   Let $(\mu_i)$ be finitely many finite measures on the real line and let $f_i$ be nonnegative integrable functions. The product of the individually tilted measures $f_i\,d\mu_i$ equals the original product measure tilted by the product density $$\prod_i f_i(x_i).$$
-- source:
--   Standard finite-product change of measure; used in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Classical BigOperators ENNReal

theorem ZeroFreeRRG.Hardcore.finite_product_density {ι : Type} [Fintype ι] (μ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (f : ι → ℝ → ℝ)
    (hpos : ∀ i x, 0 ≤ f i x) (hint : ∀ i, Integrable (f i) (μ i)) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi μ).withDensity (fun xs => ENNReal.ofReal (∏ i, f i (xs i))) := by sorry
