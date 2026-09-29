-- Prove2me | Theorems.Thm_EscapeCriterion_escape_norm_growth
-- name    : EscapeCriterion.escape_norm_growth
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:42:03.379353+00:00
-- url     : https://prove2.me/theorems/b405b9cd-6b5d-4b06-9d2d-86fdf0915d15
-- title:
--   Escape norm growth (strengthened).
-- statement:
--   **Escape norm growth (strengthened).** If a point `z` lies strictly outside the escape
--   radius of `c`, then its whole forward orbit does, and the orbit grows at least
--   geometrically with ratio `‖z‖ - 1 > 1`.
--
--   ```lean
--   theorem EscapeCriterion.escape_norm_growth(c z : ℂ) (hz : escapeRadius c < ‖z‖) (n : ℕ) :
--       escapeRadius c < ‖orbit c z n‖ ∧ (‖z‖ - 1) ^ n * ‖z‖ ≤ ‖orbit c z n‖ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EscapeCriterionIteration.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EscapeCriterionIteration.lean#L78

-- Thm stub generated from Novelty/EscapeCriterionIteration.lean
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_MandelbrotQuadraticEscape

/-!
# A formally specified escape-time test for the quadratic family

This file strengthens the escape estimates of `Novelty.MandelbrotQuadraticEscape`
(where divergence of the *critical* orbit is proved only under the a priori hypothesis
`2 < ‖c‖`) into a **complete escape criterion for arbitrary orbits** of `f_c(z) = z² + c`:

* `escapeRadius c = max 2 ‖c‖` is the standard escape radius.
* `escape_norm_growth`: once an orbit point strictly exceeds the escape radius, the whole
  forward orbit stays in the escaping region and grows geometrically,
  `(‖z‖ - 1)^n * ‖z‖ ≤ ‖orbit c z n‖`, with ratio `‖z‖ - 1 > 1`.
* `escape_tendsto_atTop`: hence the orbit norm tends to infinity — crossing the escape
  radius *once* certifies divergence.
* `escape_time_bound`: an **effective** escape time: an explicit number of iterations after
  which the orbit provably exceeds a prescribed threshold `B`.
* `bounded_iff_never_escapes`: soundness *and* completeness of the escape-time test:
  an orbit is bounded iff it never crosses the escape radius.
* `mem_Mandelbrot_iff`: `c ∈ M ↔ ∀ n, ‖critOrbit c n‖ ≤ 2` — the radius-`2` test used by
  every Mandelbrot renderer, now a theorem rather than a heuristic.
* `escapeRadius_sharp`: the radius `2` cannot be lowered (witness `c = -2`).
* Topological payoff: `Mandelbrot_eq_iInter`, `isClosed_Mandelbrot`, `isCompact_Mandelbrot`:
  the dynamical estimate converts the escape-time algorithm into the statement that `M`
  is a nested intersection of closed test sets, hence compact.
-/

open EscapeCriterion

open Filter MandelbrotEscape
open scoped Topology

/-! ## Orbits of arbitrary starting points -/







/-! ## The escape radius and the one-step growth estimate -/






/-! ## The strengthened growth theorem and divergence -/

theorem EscapeCriterion.escape_norm_growth(c z : ℂ) (hz : escapeRadius c < ‖z‖) (n : ℕ) :
    escapeRadius c < ‖orbit c z n‖ ∧ (‖z‖ - 1) ^ n * ‖z‖ ≤ ‖orbit c z n‖ := by sorry
