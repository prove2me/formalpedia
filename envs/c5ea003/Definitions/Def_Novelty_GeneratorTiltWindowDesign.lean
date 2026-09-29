-- Prove2me | Definitions.Def_Novelty_GeneratorTiltWindowDesign
-- name    : Novelty_GeneratorTiltWindowDesign
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:28:41.645369+00:00
-- url     : https://prove2.me/theorems/065a5fa8-3e94-4a9f-8cbf-edb41022e1d3
-- title:
--   Aether Catalog definitions — Novelty_GeneratorTiltWindowDesign
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.GeneratorTiltWindowDesign`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/GeneratorTiltWindowDesign.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_GeneratorTiltRatio
/-
# Can a different window rescue the ascending scan?  A no-go theorem

Cycle 1 (`Novelty.GeneratorTiltRatio`) fixed the *canonical* window `(√(N/2), √N]`, whose
multiplier is `R = 2`, and found the tie ratio `r★ = 24 - 16√2 ≈ 1.3726`.  The obvious
follow-up is a design question: the window multiplier is a free parameter — scanning
`(√(N/R), √N]` upwards is well defined whenever the generator guarantees `q < R p` — so can
a *wider* (or narrower) window make the ascending order win on the near-balanced populations
that deployed generators actually produce?

This file answers **no**, quantitatively.  For the `R`-window the tilt law is
`zGen R r = (r^{-1/2} - R^{-1/2}) / (1 - R^{-1/2})`, and:

* `zGen_criticalRatioGen`, `half_lt_zGen_iff` — the tie ratio for multiplier `R` is exactly
  `r★(R) = 4R / (1 + √R)²`, and ratios below it are top-heavy (ascending loses);
* `one_lt_criticalRatioGen` — `r★(R) > 1` for **every** `R > 1`: whatever the window, an
  interval of ratios just above `1` is adversarial to the ascending scan.  Since real
  generators concentrate the ratio near `1`, no window design removes the adversarial tilt;
* `criticalRatioGen_lt_four` — moreover `r★(R) < 4` for every `R`: the tie point can never be
  pushed past ratio `4`, so the "widen the window" strategy is capped;
* `integral_zGen` / `mean_zGen_uniform` — the exact mean tilt of a *ratio-uniform* pool on
  `[1, R]` is `1/(1 + √R)`, always `< 1/2`.  Artificial ratio-uniform pools are bottom-heavy
  for every window multiplier, which is precisely why they are the only place a
  window-ascending advantage was ever seen.  (At `R = 2` this recovers `√2 - 1`.)

Taken together with `Novelty.GeneratorTiltSynthesis`, the scope boundary is now closed on
both sides: bottom-heavy = artificial ratio-spread pools, top-heavy = near-balanced deployed
pools, for every admissible window.
-/

namespace GeneratorTilt

open Real

/-- Tilt law for the window `(√(N/R), √N]` of multiplier `R`. -/
noncomputable def zGen (R r : ℝ) : ℝ :=
  (1 / Real.sqrt r - 1 / Real.sqrt R) / (1 - 1 / Real.sqrt R)

/-- Tie ratio for window multiplier `R`: `4R / (1 + √R)²`. -/
noncomputable def criticalRatioGen (R : ℝ) : ℝ := 4 * R / (1 + Real.sqrt R) ^ 2


section
variable {R : ℝ}




/-! ## Values, monotonicity, the tie ratio -/







/-! ## The no-go bounds on the tie ratio -/





/-! ## Ratio-uniform pools are bottom-heavy for every window -/







end

end GeneratorTilt


