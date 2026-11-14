-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_size_bias_gap_weighted_identity
-- name    : ZeroFreeRRG.Hardcore.size_bias_gap_weighted_identity
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:56:50.83021+00:00
-- url     : https://prove2.me/theorems/3de8a166-7ed6-47c8-9db2-73406b8f9ce7
-- title:
--   Size-bias supermodular gap as a weighted expectation
-- statement:
--   For independent copies of a coupling between a nonnegative integrable law and its size-biased law, the expected supermodular gap for any measurable test function equals the corresponding alternating sum of expectations under the original product law, weighted by the selected-coordinate products. The formal statement gives the complete identity and requires integrability of the selected-coordinate tests.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Classical BigOperators ENNReal

theorem ZeroFreeRRG.Hardcore.size_bias_gap_weighted_identity (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ x)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hfst : Measure.map Prod.fst π = μ)
    (hsnd : Measure.map Prod.snd π = μ.withDensity (fun x => ENNReal.ofReal x))
    (K : (Fin d → ℝ) → ℝ) (hK : Measurable K)
    (hgi : ∀ S : Finset (Fin d), Integrable
      (fun xs : Fin d → ℝ × ℝ => K (fun i => if i ∈ S then (xs i).2 else (xs i).1))
      (Measure.pi fun _ : Fin d => π)) :
    let g := fun (xs : Fin d → ℝ × ℝ) (S : Finset (Fin d)) =>
      K (fun i => if i ∈ S then (xs i).2 else (xs i).1)
    let w := fun (xs : Fin d → ℝ) (S : Finset (Fin d)) =>
      (∏ i, if i ∈ S then max (xs i) 0 else 1) * K xs
    (∫ xs, g xs Finset.univ - g xs ∅ - ∑ i, (g xs {i}-g xs ∅)
      ∂(Measure.pi fun _ : Fin d => π)) =
    ∫ xs, w xs Finset.univ - w xs ∅ - ∑ i, (w xs {i}-w xs ∅)
      ∂(Measure.pi fun _ : Fin d => μ) := by sorry
