-- Prove2me | Theorems.Thm_EscapeCriterion_continuousOn_potentialSeq
-- name    : EscapeCriterion.continuousOn_potentialSeq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:43:47.782102+00:00
-- url     : https://prove2.me/theorems/31d1bae2-4e6f-4e37-8c5a-866ce385069f
-- title:
--   ContinuousOn potentialSeq
-- statement:
--   Formal statement of `EscapeCriterion.continuousOn_potentialSeq` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem EscapeCriterion.continuousOn_potentialSeq(n : ℕ) :
--       ContinuousOn (potentialSeq n) {c : ℂ | 2 < ‖c‖} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EscapeRateContinuity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EscapeRateContinuity.lean#L103

-- Thm stub generated from Novelty/EscapeRateContinuity.lean
import Mathlib
import Definitions.Def_Novelty_EscapeRateContinuity
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





/-! ## Continuity of the Douady–Hubbard potential -/

theorem EscapeCriterion.continuousOn_potentialSeq(n : ℕ) :
    ContinuousOn (potentialSeq n) {c : ℂ | 2 < ‖c‖} := by sorry
