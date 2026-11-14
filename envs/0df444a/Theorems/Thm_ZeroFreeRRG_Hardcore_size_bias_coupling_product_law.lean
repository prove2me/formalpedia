-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_size_bias_coupling_product_law
-- name    : ZeroFreeRRG.Hardcore.size_bias_coupling_product_law
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:53:08.207194+00:00
-- url     : https://prove2.me/theorems/a943ea7a-febf-4bf4-93cc-2c0e8bdabb0a
-- title:
--   Selected coordinates of independent size-bias couplings
-- statement:
--   Let $(X_i,Y_i)$ be independent copies of a coupling of a nonnegative law $\mu$ and its size-biased law $x\,d\mu(x)$. For any set of indices $S$, form the vector using $Y_i$ for $i\in S$ and $X_i$ otherwise. Its distribution is the product law $\mu^{\otimes d}$ tilted by $$\prod_{i\in S}x_i.$$ The formal statement uses $\max(x_i,0)$, which agrees almost surely with $x_i$.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, equation (25), pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Classical BigOperators ENNReal

theorem ZeroFreeRRG.Hardcore.size_bias_coupling_product_law (d : ℕ) (S : Finset (Fin d)) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ x)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hfst : Measure.map Prod.fst π = μ)
    (hsnd : Measure.map Prod.snd π = μ.withDensity (fun x => ENNReal.ofReal x)) :
    Measure.map (fun xs : Fin d → ℝ × ℝ => fun i => if i ∈ S then (xs i).2 else (xs i).1)
      (Measure.pi fun _ : Fin d => π) =
    (Measure.pi fun _ : Fin d => μ).withDensity
      (fun xs => ENNReal.ofReal (∏ i, if i ∈ S then max (xs i) 0 else 1)) := by sorry
