-- Prove2me | Theorems.Thm_ZCDPtoGDP_Sharp_Supplement_lemma_21
-- name    : ZCDPtoGDP.Sharp.Supplement.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:10:28.535305+00:00
-- url     : https://prove2.me/theorems/21c4534a-418e-44ae-b7ac-a2841a36a143
-- title:
--   Lemma 21 — Gaussian integral identity
-- statement:
--   Let $\Theta$ have the uniform law on $[0,\pi/4]$ on any probability space, and put $A(\theta)=1/(8\cos^2\theta)$. For every real $s\ge0$,
--   $$4\Phi(\sqrt{s}/2)\Phi(-\sqrt{s}/2)=\frac4\pi\int_0^{\pi/4}\exp\!\left(-\frac{s}{8\cos^2\theta}\right)\,d\theta=\mathbb E\!\left[e^{-sA(\Theta)}\right].$$
--   Here $\Phi$ is the published standard normal CDF. At $s=0$ all three quantities equal one. Both the interval integral and the expectation are part of the conclusion.
--
--   This identity supports Theorem 7 and the analytic work for Theorem 15. The uniform law and the bounded reciprocal cosine square ensure that both integrals are actual finite integrals.
--
--   Differences from the source:
--   - encoding: Θ has the uniform law on [0,π/4] → HasLaw Θ angularLaw P on an arbitrary probability space; reason: HasLaw includes almost-everywhere measurability and equality of the pushforward law, preventing a nonmeasurable-map default
-- source:
--   Yu-Wei Chen, Aaradhya Pandey, Jordan Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), Lemma 21, p. 23; proof pp. 23. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf

import Mathlib
import Definitions.Def_ZCDPtoGDP_Sharp_Privacy
import Definitions.Def_ZCDPtoGDP_Sharp_Supplement_Angular

open MeasureTheory ProbabilityTheory

namespace ZCDPtoGDP.Sharp.Supplement

/-- Lemma 21 (Gaussian integral identity), p. 23. The law hypothesis includes
almost-everywhere measurability. Boundedness on the angular interval ensures
integrability of both integrands without adding an integrability hypothesis. -/
theorem lemma_21 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Θ : Ω → ℝ) (hΘ : HasLaw Θ angularLaw P)
    (s : ℝ) (hs : 0 ≤ s) :
    4 * stdNormalCDF (Real.sqrt s / 2) * stdNormalCDF (-Real.sqrt s / 2) =
      (4 / Real.pi) * ∫ θ in (0 : ℝ)..(Real.pi / 4),
        Real.exp (-s / (8 * Real.cos θ ^ 2)) ∧
    (4 / Real.pi) * (∫ θ in (0 : ℝ)..(Real.pi / 4),
        Real.exp (-s / (8 * Real.cos θ ^ 2))) =
      ∫ ω, Real.exp (-s * angularA (Θ ω)) ∂P := by sorry

end ZCDPtoGDP.Sharp.Supplement
