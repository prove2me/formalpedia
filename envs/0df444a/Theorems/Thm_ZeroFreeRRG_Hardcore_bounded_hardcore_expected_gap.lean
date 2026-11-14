-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_bounded_hardcore_expected_gap
-- name    : ZeroFreeRRG.Hardcore.bounded_hardcore_expected_gap
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:37:41.060199+00:00
-- url     : https://prove2.me/theorems/49b54c1f-f8ff-4556-81fc-517ac4314fe6
-- title:
--   Positive expected log-product gap for bounded ordered pairs
-- statement:
--   Let $d\ge2$ and $\theta>0$. Suppose independent pairs $(X_i,Y_i)$ satisfy $0\le X_i\le Y_i\le C$ almost surely, and both $X_i<Y_i$ and $X_i>0$ have positive probability. Then the expected log-product supermodular gap between the all-upper, all-lower and single-coordinate-upper vectors is strictly positive. Boundedness supplies integrability. This is the strict expected gap in the hardcore Bethe monotonicity argument.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 30.

import Mathlib
open scoped Classical BigOperators
open MeasureTheory Set

namespace ZeroFreeRRG.Hardcore
theorem bounded_hardcore_expected_gap (d : ℕ) (hd : 2 ≤ d) (θ C : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hbound : ∀ᵐ p ∂π, 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ C)
    (hs : 0 < π {p | p.1 < p.2}) (hp : 0 < π {p | 0 < p.1}) :
    let g := fun (xs : Fin d → ℝ × ℝ) (S : Finset (Fin d)) =>
        Real.log (1+θ*∏ a, if a ∈ S then (xs a).2 else (xs a).1)
    0 < ∫ xs, g xs Finset.univ - g xs ∅ - ∑ i, (g xs {i}-g xs ∅)
      ∂(Measure.pi fun _ : Fin d => π) := by sorry
end ZeroFreeRRG.Hardcore
