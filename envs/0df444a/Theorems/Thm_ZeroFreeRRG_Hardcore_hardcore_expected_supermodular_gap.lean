-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_expected_supermodular_gap
-- name    : ZeroFreeRRG.Hardcore.hardcore_expected_supermodular_gap
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:32:34.977204+00:00
-- url     : https://prove2.me/theorems/9578d266-c3f0-4657-b214-ce129fe1f197
-- title:
--   Strict expected log-product gap under ordered coupling
-- statement:
--   Let $d\ge2$, $\theta>0$, and let independent pairs $(X_i,Y_i)$ have an ordered nonnegative law with $X_i<Y_i$ and $X_i>0$ each occurring with positive probability. Form the log-product supermodular gap between all-upper, all-lower, and single-coordinate-upper vectors. If this gap is integrable, its expectation is strictly positive. This is the positive expectation step in the hardcore Bethe monotonicity argument.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 30.

import Mathlib
open scoped Classical BigOperators
open MeasureTheory Set

namespace ZeroFreeRRG.Hardcore
theorem hardcore_expected_supermodular_gap (d : ℕ) (hd : 2 ≤ d) (θ : ℝ) (hθ : 0 < θ)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (horder : ∀ᵐ p ∂π, 0 ≤ p.1 ∧ p.1 ≤ p.2)
    (hs : 0 < π {p | p.1 < p.2}) (hp : 0 < π {p | 0 < p.1})
    (hI : let g := fun (xs : Fin d → ℝ × ℝ) (S : Finset (Fin d)) =>
        Real.log (1+θ*∏ a, if a ∈ S then (xs a).2 else (xs a).1)
      Integrable (fun xs => g xs Finset.univ - g xs ∅ - ∑ i, (g xs {i}-g xs ∅))
        (Measure.pi fun _ : Fin d => π)) :
    let g := fun (xs : Fin d → ℝ × ℝ) (S : Finset (Fin d)) =>
        Real.log (1+θ*∏ a, if a ∈ S then (xs a).2 else (xs a).1)
    0 < ∫ xs, g xs Finset.univ - g xs ∅ - ∑ i, (g xs {i}-g xs ∅)
      ∂(Measure.pi fun _ : Fin d => π) := by sorry
end ZeroFreeRRG.Hardcore
