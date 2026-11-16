-- Prove2me | Theorems.Thm_ZCDPtoGDP_Sharp_Supplement_theorem_7
-- name    : ZCDPtoGDP.Sharp.Supplement.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:11:01.325932+00:00
-- url     : https://prove2.me/theorems/31f202e1-94f4-41a3-a1eb-72ddb4ae84eb
-- title:
--   Theorem 7 — Shape and limiting scales of the zCDP conversion
-- statement:
--   Let $t_\rho\ge0$ solve $\rho=t_\rho\tanh(t_\rho/2)$, and write $\mu_{\mathrm{zCDP}}(\rho)=2\Phi^{-1}(\sigma(t_\rho))$. On $[0,\infty)$ the conversion is strictly increasing and its square is strictly convex. Its ratio to $\sqrt\rho$ is strictly increasing on $(0,\infty)$, with
--   $$\lim_{\rho\downarrow0}\frac{\mu_{\mathrm{zCDP}}(\rho)}{\sqrt\rho}=\sqrt\pi,\qquad \lim_{\rho\to\infty}\frac{\mu_{\mathrm{zCDP}}(\rho)}{\sqrt\rho}=\sqrt8.$$
--   For every $\rho\ge0$,
--   $$\sqrt{\pi\rho}\le\mu_{\mathrm{zCDP}}(\rho)\le\sqrt{8\rho}.$$
--   Strict convexity includes segments starting at zero; at zero both bounds are equalities. The limits give the sharp endpoint scales, while the shape assertions underlie the paper's privacy accounting comparisons.
--
--   Differences from the source:
--   - encoding: tρ is the unique nonnegative root in Theorem 6 → tRho is the infimum of that singleton root set, extended by zero below zero; reason: the published calibration makes this exactly the source function on every asserted budget
--   - encoding: the limit at zero is from the right and ratios have positive domain → nhdsWithin 0 (Set.Ioi 0) for the limit and Set.Ioi 0 for ratio monotonicity; reason: division at zero plays no role, while shape assertions still include zero
-- source:
--   Yu-Wei Chen, Aaradhya Pandey, Jordan Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), Theorem 7, p. 6; proof pp. 23–26. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf

import Mathlib
import Definitions.Def_ZCDPtoGDP_Sharp_Supplement_Conversions

open Filter
open scoped Topology

namespace ZCDPtoGDP.Sharp.Supplement

/-- Theorem 7, p. 6 (repeated p. 23; proof pp. 24–26).
Every clause uses the explicit conversion, with closed-half-line strict convexity
and positive-half-line ratios. The zero limit is from the right. -/
theorem theorem_7 :
    StrictMonoOn muZCDP (Set.Ici 0) ∧
    Tendsto (fun ρ => muZCDP ρ / Real.sqrt ρ) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (Real.sqrt Real.pi)) ∧
    Tendsto (fun ρ => muZCDP ρ / Real.sqrt ρ) atTop (𝓝 (Real.sqrt 8)) ∧
    StrictConvexOn ℝ (Set.Ici 0) (fun ρ => muZCDP ρ ^ 2) ∧
    StrictMonoOn (fun ρ => muZCDP ρ / Real.sqrt ρ) (Set.Ioi 0) ∧
    ∀ ρ : ℝ, 0 ≤ ρ →
      Real.sqrt (Real.pi * ρ) ≤ muZCDP ρ ∧ muZCDP ρ ≤ Real.sqrt (8 * ρ) := by sorry

end ZCDPtoGDP.Sharp.Supplement
