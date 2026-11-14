-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_mean_one_bias_dominates
-- name    : ZeroFreeRRG.Hardcore.mean_one_bias_dominates
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:14:30.416211+00:00
-- url     : https://prove2.me/theorems/0615bf86-e248-415d-a830-8e48a896a46d
-- title:
--   Mean-one bias raises monotone expectations
-- statement:
--   Let $W$ be an integrable real random variable with mean one, and let $g$ be nondecreasing with $g(W)$ and $Wg(W)$ integrable. Then $\mathbb E[g(W)]\le\mathbb E[Wg(W)]$. When $W\ge0$, the right side is the expectation under the size-biased law, giving its stochastic domination over the original law as used in the hardcore Bethe comparison.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 30.

import Mathlib
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
theorem mean_one_bias_dominates (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : ℝ → ℝ)
    (hmono : Monotone g) (hW : Integrable (fun x => x) μ) (hg : Integrable g μ)
    (hWg : Integrable (fun x => x*g x) μ) (hmean : (∫ x, x ∂μ) = 1) :
    (∫ x, g x ∂μ) ≤ ∫ x, x*g x ∂μ := by sorry
end ZeroFreeRRG.Hardcore
