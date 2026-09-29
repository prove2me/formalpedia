-- Prove2me | Theorems.Thm_GeneratorTilt_integral_zGen
-- name    : GeneratorTilt.integral_zGen
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:58:59.432774+00:00
-- url     : https://prove2.me/theorems/ec9e9e82-8987-486b-9345-a18ce2b910bd
-- title:
--   Total tilt of a ratio-uniform pool on `[1, R]`.
-- statement:
--   Total tilt of a ratio-uniform pool on `[1, R]`.
--
--   ```lean
--   theorem GeneratorTilt.integral_zGen(hR : 1 < R) :
--       (∫ r in (1:ℝ)..R, zGen R r) = (R - 1) / (1 + Real.sqrt R) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/GeneratorTiltWindowDesign.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/GeneratorTiltWindowDesign.lean#L178

-- Thm stub generated from Novelty/GeneratorTiltWindowDesign.lean
import Mathlib
import Definitions.Def_Novelty_GeneratorTiltRatio
import Definitions.Def_Novelty_GeneratorTiltWindowDesign
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

open GeneratorTilt

open Real




variable {R : ℝ}




/-! ## Values, monotonicity, the tie ratio -/







/-! ## The no-go bounds on the tie ratio -/





/-! ## Ratio-uniform pools are bottom-heavy for every window -/

theorem GeneratorTilt.integral_zGen(hR : 1 < R) :
    (∫ r in (1:ℝ)..R, zGen R r) = (R - 1) / (1 + Real.sqrt R) := by sorry
