-- Prove2me | Definitions.Def_Novelty_EscapeRateContinuity
-- name    : Novelty_EscapeRateContinuity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:25:13.01778+00:00
-- url     : https://prove2.me/theorems/cc10021a-6929-44be-9cac-3536c22cb7ef
-- title:
--   Aether Catalog definitions — Novelty_EscapeRateContinuity
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.EscapeRateContinuity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/EscapeRateContinuity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeRateGreenFunction
import Definitions.Def_Novelty_FilledJuliaCompact

/-!
# Uniform convergence and continuity of the escape rate

Fifth iteration of the escape-criterion thread. The increment bound
`dist_logOrbitSeq_le` is *uniform* in both the point `z` and the parameter `c`: the
`n`-th term of the defining sequence of the escape rate differs from its limit by at most
`2^{-n}`, whatever escaping `z` and whatever `c`. Consequently the convergence is uniform
on the whole escaping region, and the escape rate inherits continuity from the polynomial
iterates.

Main results:

* `abs_logOrbitSeq_sub_escapeRate_le`: `|2^{-n} log ‖z_n‖ - G_c(z)| ≤ 2^{-n}`, an explicit
  error bound for the numerical computation of the escape rate.
* `tendstoUniformlyOn_logOrbitSeq`: uniform convergence on the escaping region.
* `continuousOn_escapeRate`: `G_c` is continuous on `{z | ‖z‖ > max 2 ‖c‖}`.
* `continuousOn_mandelbrotPotential`: the Douady–Hubbard potential `G_M` is continuous on
  `{c | ‖c‖ > 2}`, obtained from the same uniform estimate in the *parameter*.
-/

namespace EscapeCriterion

open Filter MandelbrotEscape
open scoped Topology

variable {c z : ℂ}





/-! ## Continuity of the Douady–Hubbard potential -/

/-- The truncations of the potential, `2^{-(n+1)} log ‖z_{n+2}(c)‖`. -/
noncomputable def potentialSeq (n : ℕ) (c : ℂ) : ℝ := logOrbitSeq c (orbit c 0 2) n / 2





end EscapeCriterion


