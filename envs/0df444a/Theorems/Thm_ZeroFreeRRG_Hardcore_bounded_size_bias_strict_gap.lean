-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_bounded_size_bias_strict_gap
-- name    : ZeroFreeRRG.Hardcore.bounded_size_bias_strict_gap
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:45:09.488195+00:00
-- url     : https://prove2.me/theorems/f99e3d26-9253-4488-a152-6b043f90ac42
-- title:
--   Strict expected log-product gap for a bounded nontrivial mean-one law
-- statement:
--   Let $d\geq2$, $\theta>0$, and let $\mu$ be a probability law on $[0,C]$ with mean one, distinct from the point mass at one. There is a coupling of $\mu$ with its size-biased law such that independent copies have a strictly positive expected log-product supermodular gap. The formal statement displays the full gap.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.bounded_size_bias_strict_gap (d : ℕ) (hd : 2 ≤ d) (θ C : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hbound : ∀ᵐ x ∂μ, 0 ≤ x ∧ x ≤ C)
    (hint : Integrable (fun x : ℝ => x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1) (hne : μ ≠ Measure.dirac 1) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      Measure.map Prod.fst π = μ ∧
      Measure.map Prod.snd π = μ.withDensity (fun x => ENNReal.ofReal x) ∧
      let g := fun (xs : Fin d → ℝ × ℝ) (S : Finset (Fin d)) =>
        Real.log (1+θ*∏ a, if a ∈ S then (xs a).2 else (xs a).1)
      0 < ∫ xs, g xs Finset.univ - g xs ∅ - ∑ i, (g xs {i}-g xs ∅)
        ∂(Measure.pi fun _ : Fin d => π) := by sorry
