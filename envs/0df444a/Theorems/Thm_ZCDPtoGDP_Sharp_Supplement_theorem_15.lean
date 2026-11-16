-- Prove2me | Theorems.Thm_ZCDPtoGDP_Sharp_Supplement_theorem_15
-- name    : ZCDPtoGDP.Sharp.Supplement.theorem_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:12:05.223954+00:00
-- url     : https://prove2.me/theorems/a6144637-8646-4e1e-b7c4-6d7710127eef
-- title:
--   Theorem 15 — Shape and sharp scales of the bounded-range conversion
-- statement:
--   Write $\mu_{\mathrm{BR}}(\varepsilon)=2\Phi^{-1}(\sigma(\varepsilon/2))$. On $[0,\infty)$ this function is strictly increasing and strictly concave, and its square is strictly convex. On $(0,\infty)$, $\mu_{\mathrm{BR}}(\varepsilon)^2/\varepsilon$ is strictly increasing and $\mu_{\mathrm{BR}}(\varepsilon)/\varepsilon$ is strictly decreasing. The limiting scales are
--   $$\lim_{\varepsilon\downarrow0}\frac{\mu_{\mathrm{BR}}(\varepsilon)}{\varepsilon}=\sqrt{\pi/8},\qquad \lim_{\varepsilon\to\infty}\frac{\mu_{\mathrm{BR}}(\varepsilon)}{\sqrt\varepsilon}=2.$$
--   For every $\varepsilon\ge0$,
--   $$\mu_{\mathrm{BR}}(\varepsilon)\le\min\{\sqrt{\pi/8}\,\varepsilon,\ 2\sqrt\varepsilon\}.$$
--   Both coefficients are optimal: for every $c<\sqrt{\pi/8}$ there exists $\varepsilon>0$ with $c\varepsilon<\mu_{\mathrm{BR}}(\varepsilon)$, and for every $c<2$ there exists $\varepsilon>0$ with $c\sqrt\varepsilon<\mu_{\mathrm{BR}}(\varepsilon)$.
--
--   The closed-half-line shape assertions include segments with an endpoint at zero. The result supplies the distinct linear small-budget and square-root large-budget scales and the shape properties used in the paper's logistic privacy accounting comparisons.
--
--   Differences from the source:
--   - encoding: limits from the right and positive-domain ratios → a right-neighborhood filter at zero, with ratio monotonicity only on Set.Ioi 0; reason: zero denominators are outside all ratio claims; shape and bounds include zero
--   - encoding: both constants sharp by the two limits → every smaller coefficient is exceeded at some positive budget; reason: this spells out optimality of the two universal upper-bound coefficients without weakening either limit
-- source:
--   Yu-Wei Chen, Aaradhya Pandey, Jordan Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), Theorem 15, p. 9; proof pp. 26–27. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf

import Mathlib
import Definitions.Def_ZCDPtoGDP_Sharp_Supplement_Conversions

open Filter
open scoped Topology

namespace ZCDPtoGDP.Sharp.Supplement

/-- Theorem 15, p. 9 (proof pp. 26–27), including optimality of both
constants: every smaller coefficient fails somewhere on the positive half-line. -/
theorem theorem_15 :
    StrictMonoOn muBR (Set.Ici 0) ∧
    StrictConcaveOn ℝ (Set.Ici 0) muBR ∧
    Tendsto (fun ε => muBR ε / ε) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (Real.sqrt (Real.pi / 8))) ∧
    Tendsto (fun ε => muBR ε / Real.sqrt ε) atTop (𝓝 2) ∧
    StrictConvexOn ℝ (Set.Ici 0) (fun ε => muBR ε ^ 2) ∧
    StrictMonoOn (fun ε => muBR ε ^ 2 / ε) (Set.Ioi 0) ∧
    StrictAntiOn (fun ε => muBR ε / ε) (Set.Ioi 0) ∧
    (∀ ε : ℝ, 0 ≤ ε →
      muBR ε ≤ min (Real.sqrt (Real.pi / 8) * ε) (2 * Real.sqrt ε)) ∧
    (∀ c : ℝ, c < Real.sqrt (Real.pi / 8) → ∃ ε : ℝ, 0 < ε ∧ c * ε < muBR ε) ∧
    (∀ c : ℝ, c < 2 → ∃ ε : ℝ, 0 < ε ∧ c * Real.sqrt ε < muBR ε) := by sorry

end ZCDPtoGDP.Sharp.Supplement
