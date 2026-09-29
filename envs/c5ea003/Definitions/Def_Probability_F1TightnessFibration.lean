-- Prove2me | Definitions.Def_Probability_F1TightnessFibration
-- name    : Probability_F1TightnessFibration
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:13:52.316742+00:00
-- url     : https://prove2.me/theorems/be6c738b-8e5c-48f5-b8a3-ea1054e10db0
-- title:
--   Aether Catalog definitions — Probability_F1TightnessFibration
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.F1TightnessFibration`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/F1TightnessFibration.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_F1TightnessCore

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

namespace F1Tightness

open Finset

variable {M : ℕ}




/-! ## The two extreme profiles -/

/-- All the mass on the first cell. -/
noncomputable def deltaFirst (M : ℕ) : Fin M → ℝ := fun i => if (i : ℕ) = 0 then 1 else 0

/-- All the mass on the last cell. -/
noncomputable def deltaLast (M : ℕ) : Fin M → ℝ := fun i => if (i : ℕ) = M - 1 then 1 else 0










end F1Tightness


