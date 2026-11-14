-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_size_bias_ordered_coupling_strict
-- name    : ZeroFreeRRG.Hardcore.size_bias_ordered_coupling_strict
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:22:53.254393+00:00
-- url     : https://prove2.me/theorems/73d129df-288c-4bf1-843f-8d485b9f8d9a
-- title:
--   Strictness of an ordered size-bias coupling
-- statement:
--   Let $\mu$ be a nonnegative probability law different from the point mass at one. Suppose a measure $\pi$ couples $\mu$ to its size-biased measure and is supported on pairs $x\le y$. Then $\pi\{(x,y):x<y\}>0$. Thus the ordered size-bias coupling used in the hardcore Bethe comparison is strict with positive probability whenever the original law is nontrivial.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 30.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

namespace ZeroFreeRRG.Hardcore
theorem size_bias_ordered_coupling_strict (μ : Measure ℝ) [IsProbabilityMeasure μ] (π : Measure (ℝ × ℝ))
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x) (hne : μ ≠ Measure.dirac 1)
    (hfst : Measure.map Prod.fst π = μ)
    (hsnd : Measure.map Prod.snd π = μ.withDensity (fun x => ENNReal.ofReal x))
    (horder : ∀ᵐ p ∂π, p.1 ≤ p.2) : 0 < π {p | p.1 < p.2} := by sorry
end ZeroFreeRRG.Hardcore
