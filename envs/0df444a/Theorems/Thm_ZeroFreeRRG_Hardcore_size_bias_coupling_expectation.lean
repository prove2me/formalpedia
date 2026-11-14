-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_size_bias_coupling_expectation
-- name    : ZeroFreeRRG.Hardcore.size_bias_coupling_expectation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:54:19.272446+00:00
-- url     : https://prove2.me/theorems/57f70dd9-1130-4558-86e9-273e14f3c614
-- title:
--   Expectation under selected size-biased coordinates
-- statement:
--   For independent copies of a coupling of a nonnegative integrable law $\mu$ and its size-biased law, select the size-biased coordinate in an index set $S$ and the original coordinate elsewhere. For any measurable real-valued function $K$, its integral under the selected vector equals its integral under $\mu^{\otimes d}$ weighted by $$\prod_{i\in S}\max(x_i,0).$$ The identity also holds under Lean’s convention for nonintegrable Bochner integrals.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Classical BigOperators ENNReal

theorem ZeroFreeRRG.Hardcore.size_bias_coupling_expectation (d : ℕ) (S : Finset (Fin d)) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ x)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hfst : Measure.map Prod.fst π = μ)
    (hsnd : Measure.map Prod.snd π = μ.withDensity (fun x => ENNReal.ofReal x))
    (K : (Fin d → ℝ) → ℝ) (hK : Measurable K) :
    (∫ xs : Fin d → ℝ × ℝ, K (fun i => if i ∈ S then (xs i).2 else (xs i).1)
       ∂(Measure.pi fun _ : Fin d => π)) =
    ∫ xs : Fin d → ℝ, (∏ i, if i ∈ S then max (xs i) 0 else 1) * K xs
       ∂(Measure.pi fun _ : Fin d => μ) := by sorry
