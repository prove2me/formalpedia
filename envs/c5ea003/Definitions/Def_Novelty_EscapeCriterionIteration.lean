-- Prove2me | Definitions.Def_Novelty_EscapeCriterionIteration
-- name    : Novelty_EscapeCriterionIteration
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:22:39.825106+00:00
-- url     : https://prove2.me/theorems/280382e1-aafb-479f-a8b2-ec9113b1cd52
-- title:
--   Aether Catalog definitions — Novelty_EscapeCriterionIteration
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.EscapeCriterionIteration`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/EscapeCriterionIteration.lean by skeleton subtraction
import Mathlib
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

namespace EscapeCriterion

open Filter MandelbrotEscape
open scoped Topology

/-! ## Orbits of arbitrary starting points -/

/-- The orbit of an arbitrary starting point `z` under `f_c(w) = w² + c`. -/
def orbit (c z : ℂ) (n : ℕ) : ℂ := (qmap c)^[n] z






/-! ## The escape radius and the one-step growth estimate -/

/-- The standard escape radius of the parameter `c`: `max 2 ‖c‖`. -/
noncomputable def escapeRadius (c : ℂ) : ℝ := max 2 ‖c‖





/-! ## The strengthened growth theorem and divergence -/





/-! ## Soundness and completeness of the escape-time test -/

/-- The orbit of `z` under `f_c` is bounded. -/
def BoundedOrbit (c z : ℂ) : Prop := ∃ B : ℝ, ∀ n, ‖orbit c z n‖ ≤ B



/-! ## The radius-2 test for the Mandelbrot set -/



/-! ## Sharpness of the radius `2` -/




/-! ## Topological consequences: the escape-time test sets -/

/-- The `n`-th test set of the escape-time algorithm: the parameters that survive `n`
iterations of the radius-`2` test. -/
def testSet (n : ℕ) : Set ℂ := {c | ∀ k ≤ n, ‖critOrbit c k‖ ≤ 2}







end EscapeCriterion

/-!
## Lab Notes (experimental data behind the statements above)

Floating-point experiments performed before formalisation (see `ComputationalEvidence.md`
in the project root for the full protocol); these guided, but do not constitute, the proofs.

* 20 000 random pairs `(c, z₀) ∈ ([-3,3]²)²`: every orbit that crossed `max(2, ‖c‖)` had
  `‖z‖ > 10⁶` within 50 further iterations — 0 counterexamples to
  `tendsto_atTop_of_exists_escape`.
* 20 000 random escaping points: 0 violations of the one-step bound
  `‖z² + c‖ ≥ (‖z‖ - 1)‖z‖` (`qmap_norm_ge_mul`).
* 20 000 random `c` with `‖c‖ ≤ 2`: every critical orbit that exceeded `2` diverged
  (0 counterexamples to `mem_Mandelbrot_iff`).
* Growth is *much* faster than the geometric bound: for `c = 0.3 + 0.1i`, `z₀ = 2.5`,
  the orbit norms are `2.5, 6.55, 43.2, 1.87·10³, 3.49·10⁶` against the certified lower
  bounds `2.5, 3.75, 5.63, 8.44, 12.66`. This gap is exactly what
  `Novelty.EscapeDoublyExponential.log_norm_orbit_sub_one_ge` closes.
* Sharpness: the orbit of `c = -2` is `0, -2, 2, 2, …`, bounded with norm exactly `2`
  (`escapeRadius_sharp`); no radius below `2` yields a sound test.
-/


