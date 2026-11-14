-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_nontrivial_size_bias_strict_coupling
-- name    : ZeroFreeRRG.Hardcore.nontrivial_size_bias_strict_coupling
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:29:58.869209+00:00
-- url     : https://prove2.me/theorems/4e9c8dc3-b7a6-4ebd-9558-311b0e4ffcc8
-- title:
--   Strict ordered size-bias coupling and positive product event
-- statement:
--   A nonnegative integrable mean-one probability law other than $\delta_1$ has an ordered coupling with its size-biased law, with positive probability of strict inequality. Moreover, for every $d\ge2$, independent copies have positive probability of two strict pairs and positive original coordinates in all other pairs. This constructs exactly the positive-probability strict event in the hardcore part of Lemma 4.17.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 30.

import Mathlib
open MeasureTheory Set

namespace ZeroFreeRRG.Hardcore
theorem nontrivial_size_bias_strict_coupling (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x) (hint : Integrable (fun x => x) μ)
    (hmean : (∫ x, x ∂μ) = 1) (hne : μ ≠ Measure.dirac 1) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      Measure.map Prod.fst π = μ ∧
      Measure.map Prod.snd π = μ.withDensity (fun x => ENNReal.ofReal x) ∧
      (∀ᵐ p ∂π, p.1 ≤ p.2) ∧ (0 < π {p | p.1 < p.2}) ∧
      (∀ d : ℕ, ∀ hd : 2 ≤ d,
        0 < (Measure.pi fun _ : Fin d => π)
          {xs | (xs ⟨0,by omega⟩).1 < (xs ⟨0,by omega⟩).2 ∧
            (xs ⟨1,by omega⟩).1 < (xs ⟨1,by omega⟩).2 ∧
            ∀ a, a ≠ ⟨0,by omega⟩ → a ≠ ⟨1,by omega⟩ → 0 < (xs a).1}) := by sorry
end ZeroFreeRRG.Hardcore
