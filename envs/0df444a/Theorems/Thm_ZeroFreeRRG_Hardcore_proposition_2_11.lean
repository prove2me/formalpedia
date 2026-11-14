-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_proposition_2_11
-- name    : ZeroFreeRRG.Hardcore.proposition_2_11
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:17:33.663244+00:00
-- url     : https://prove2.me/theorems/7db7bbf4-4eaa-4f4c-9730-3a601c88f75b
-- title:
--   Tonelli identities for nonnegative random functions
-- statement:
--   Let $K\subseteq\mathbb C$ be compact, let $g$ be a jointly measurable nonnegative random function on $K$, and let $(\zeta_n)$ be nonnegative measurable random variables. Then the expectation of the area integral of $g$ equals the area integral of its expectation, and the expectation of the countable sum of the $\zeta_n$ equals the sum of their expectations. Integrals take values in $[0,\infty]$, so the identities also cover infinite values.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, Proposition 2.11, printed p. 18.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

namespace ZeroFreeRRG.Hardcore
theorem proposition_2_11 {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Set ℂ) (hK : IsCompact K) (g : Ω × ℂ → ℝ≥0∞) (hg : Measurable g)
    (ζ : ℕ → Ω → ℝ≥0∞) (hζ : ∀ n, Measurable (ζ n)) :
    (∫⁻ ω, ∫⁻ z in K, g (ω,z) ∂volume ∂μ) =
      (∫⁻ z in K, ∫⁻ ω, g (ω,z) ∂μ ∂volume) ∧
    (∫⁻ ω, ∑' n, ζ n ω ∂μ) = ∑' n, ∫⁻ ω, ζ n ω ∂μ := by sorry
end ZeroFreeRRG.Hardcore
