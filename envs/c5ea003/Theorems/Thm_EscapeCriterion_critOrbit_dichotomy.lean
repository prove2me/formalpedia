-- Prove2me | Theorems.Thm_EscapeCriterion_critOrbit_dichotomy
-- name    : EscapeCriterion.critOrbit_dichotomy
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:43:28.847513+00:00
-- url     : https://prove2.me/theorems/d86598d9-e4c7-448f-9f2b-54dfa854e3a2
-- title:
--   Dichotomy for the critical orbit: it either stays in the closed disk of radius `2`
-- statement:
--   **Dichotomy for the critical orbit**: it either stays in the closed disk of radius `2`
--   forever, or its norm tends to infinity. There is no intermediate behaviour.
--
--   ```lean
--   theorem EscapeCriterion.critOrbit_dichotomy(c : ℂ) :
--       (∀ n, ‖critOrbit c n‖ ≤ 2) ∨ Filter.Tendsto (fun n => ‖critOrbit c n‖) Filter.atTop Filter.atTop := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EscapeCriterionIteration.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EscapeCriterionIteration.lean#L182

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





/-! ## Soundness and completeness of the escape-time test -/




/-! ## The radius-2 test for the Mandelbrot set -/

theorem EscapeCriterion.critOrbit_dichotomy(c : ℂ) :
    (∀ n, ‖critOrbit c n‖ ≤ 2) ∨ Filter.Tendsto (fun n => ‖critOrbit c n‖) Filter.atTop Filter.atTop := by sorry
