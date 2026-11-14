-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_product_coordinate_integral
-- name    : ZeroFreeRRG.Hardcore.product_coordinate_integral
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:03:39.089935+00:00
-- url     : https://prove2.me/theorems/1ae0a49d-cd70-4fbc-82a3-65149098c436
-- title:
--   Product expectation with one distinguished coordinate
-- statement:
--   For independent identically distributed real variables $(X_j)_{j<d}$ and real functions $a_j,b$, the integral of $(\prod_j a_j(X_j))b(X_i)$ equals $$\left(\int a_i(x)b(x)\,d\mu(x)\right)\prod_{j\ne i}\left(\int a_j(x)\,d\mu(x)\right).$$ The identity follows the Bochner integral convention even when the functions are not integrable.
-- source:
--   Standard product integration identity; used in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.product_coordinate_integral (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : Fin d → ℝ → ℝ) (b : ℝ → ℝ) (i : Fin d) :
    (∫ xs : Fin d → ℝ, (∏ j, a j (xs j)) * b (xs i)
       ∂(Measure.pi fun _ : Fin d => μ)) =
      (∫ x, a i x * b x ∂μ) * ∏ j ∈ Finset.univ.erase i, (∫ x, a j x ∂μ) := by sorry
