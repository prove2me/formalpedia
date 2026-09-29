-- Prove2me | Theorems.Thm_EscapeCriterion_abs_logOrbitSeq_sub_escapeRate_le
-- name    : EscapeCriterion.abs_logOrbitSeq_sub_escapeRate_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:42:35.334873+00:00
-- url     : https://prove2.me/theorems/784fbb91-7cab-41e1-8aa3-ca77d51477d3
-- title:
--   Explicit error bound for the escape rate: truncating the defining sequence at step
-- statement:
--   **Explicit error bound** for the escape rate: truncating the defining sequence at step
--   `n` costs at most `2^{-n}`, uniformly in `c` and in the escaping point `z`.
--
--   ```lean
--   theorem EscapeCriterion.abs_logOrbitSeq_sub_escapeRate_le(hz : escapeRadius c < ‖z‖) (n : ℕ) :
--       |logOrbitSeq c z n - escapeRate c z| ≤ (1 / 2 : ℝ) ^ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EscapeRateContinuity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EscapeRateContinuity.lean#L30

-- Thm stub generated from Novelty/EscapeRateContinuity.lean
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeRateContinuity
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

open EscapeCriterion

open Filter MandelbrotEscape
open scoped Topology

variable {c z : ℂ}

theorem EscapeCriterion.abs_logOrbitSeq_sub_escapeRate_le(hz : escapeRadius c < ‖z‖) (n : ℕ) :
    |logOrbitSeq c z n - escapeRate c z| ≤ (1 / 2 : ℝ) ^ n := by sorry
