-- Prove2me | Theorems.Thm_F1Tightness_deltaLast_gapX
-- name    : F1Tightness.deltaLast_gapX
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:22:19.779479+00:00
-- url     : https://prove2.me/theorems/599c10ec-6431-422a-9282-43953f60be83
-- title:
--   The last-cell point mass attains the smallest possible slack.
-- statement:
--   The last-cell point mass attains the **smallest** possible slack.
--
--   ```lean
--   theorem F1Tightness.deltaLast_gapX{M : ℕ} (hM : 0 < M) :
--       gapX (deltaLast M) = ((M : ℝ) + 1) / (2 * (M : ℝ)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/F1TightnessFibration.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/F1TightnessFibration.lean#L156

-- Thm stub generated from Probability/F1TightnessFibration.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessFibration

/-!
# The mean-position fibration of the slack factor

The identity `gapX_eq_meanPos` of `Probability.F1TightnessCore` shows that the
slack factor `X` of an `M`-cell profile depends on the profile *only* through
the mean probe position `E_x`.  This file draws the two consequences asked for
by direction 2 of `FUTURE_DIRECTIONS.md`.

* `gapX_eq_of_meanPos_eq` — **the fibration**: two profiles with the same mean
  position have the same slack, whatever their shape.  Extremality of the slack
  is therefore a statement about the reachable set of mean positions, not about
  the profile.
* `meanPos_mem_Icc` — the reachable set is contained in `[1/(2M), (2M−1)/(2M)]`,
  and `deltaFirst_meanPos`, `deltaLast_meanPos` show both endpoints are attained
  by point masses, so the containment is an equality of extremes.
* `gapX_mem_Icc`, `deltaFirst_gapX`, `deltaLast_gapX` — the resulting exact
  range of the slack factor, `X ∈ [(M+1)/(2M), (M+1)/2]`, with both endpoints
  attained.  In particular the slack of a *sorted* pool can be as large as
  `(M+1)/2`, while it can never drop below `(M+1)/(2M) → 1/2`.
-/

open F1Tightness

open Finset

variable {M : ℕ}




/-! ## The two extreme profiles -/

theorem F1Tightness.deltaLast_gapX{M : ℕ} (hM : 0 < M) :
    gapX (deltaLast M) = ((M : ℝ) + 1) / (2 * (M : ℝ)) := by sorry
