-- Prove2me | Theorems.Thm_F1Tightness_meanPos_eq_half_add
-- name    : F1Tightness.meanPos_eq_half_add
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:22:20.774728+00:00
-- url     : https://prove2.me/theorems/94e8a848-162e-43d2-a3e1-f08b169942f4
-- title:
--   The mean position splits off its minimal value `1/(2M)`: the remainder is
-- statement:
--   The mean position splits off its minimal value `1/(2M)`: the remainder is
--   the index-weighted mass.
--
--   ```lean
--   theorem F1Tightness.meanPos_eq_half_add{p : Fin M → ℝ} (hM : 0 < M)
--       (hsum : ∑ i : Fin M, p i = 1) :
--       meanPos p = 1 / (2 * (M : ℝ)) + ∑ i : Fin M, (((i : ℕ) : ℝ) / (M : ℝ)) * p i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/F1TightnessPolytope.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/F1TightnessPolytope.lean#L46

-- Thm stub generated from Probability/F1TightnessPolytope.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessFibration
import Definitions.Def_Probability_F1TightnessPolytope

/-!
# The constrained mean-position polytope of the slack factor

`Probability.F1TightnessFibration` solved the *unconstrained* extremal problem
for the slack factor `X`: since `X` depends on the profile only through the mean
probe position `E_x`, and the reachable mean positions form the interval
`[1/(2M), (2M−1)/(2M)]`, the reachable slacks are exactly
`[(M+1)/(2M), (M+1)/2]`.

Direction 3 of `FUTURE_DIRECTIONS.md` asks for the same computation under the
measured *tail* constraint: the profile must place at least a mass `m` on the
cells from index `K` on (the "edge mass bounded below" constraint of the
measured positional profile).  This file closes that question for a single
linear tail constraint.

* `edgeMass` — the mass on the cells of index `≥ K`.
* `meanPos_ge_of_edgeMass` — the sharp linear-programming bound
  `E_x ≥ (1/2 + K·m)/M` for every admissible profile.
* `gapX_le_of_edgeMass` — the resulting constraint on the slack,
  `X ≤ (M+1)/(2·K·m + 2)`.
* `pairProfile` — the two-cell profile `(1−m)·δ_a + m·δ_b`; the bound above is
  attained by `pairProfile 0 K m`, so the extremal profile of the constrained
  linear programme is supported on **at most two cells**, as conjectured.
* `constrained_gapX_range_sharp` — the packaged statement: under the tail
  constraint the reachable slacks are exactly `[(M+1)/(2M), (M+1)/(2·K·m+2)]`,
  both endpoints attained.
* `edgeMass_bound_of_gapX` — read backwards, a *measured* slack bounds the
  admissible edge mass: `K·m ≤ ((M+1)/X − 2)/2`.  This is the promised transfer
  of the booked CI on `Λ` into a constraint on the prior itself.
-/

open F1Tightness

open Finset

variable {M : ℕ}

theorem F1Tightness.meanPos_eq_half_add{p : Fin M → ℝ} (hM : 0 < M)
    (hsum : ∑ i : Fin M, p i = 1) :
    meanPos p = 1 / (2 * (M : ℝ)) + ∑ i : Fin M, (((i : ℕ) : ℝ) / (M : ℝ)) * p i := by sorry
