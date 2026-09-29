-- Prove2me | Definitions.Def_Probability_F1TightnessPolytope
-- name    : Probability_F1TightnessPolytope
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:29.283888+00:00
-- url     : https://prove2.me/theorems/298cb19a-6d14-4964-b1c5-f69574272254
-- title:
--   Aether Catalog definitions — Probability_F1TightnessPolytope
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.F1TightnessPolytope`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/F1TightnessPolytope.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessFibration

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

namespace F1Tightness

open Finset

variable {M : ℕ}

/-- The **edge mass** at cut `K`: the probability the target sits in a cell of
index `≥ K`. -/
noncomputable def edgeMass (K : ℕ) (p : Fin M → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin M => K ≤ (i : ℕ)), p i




/-! ## Attainment by a two-cell profile -/

/-- The two-cell profile `(1−m)·δ_a + m·δ_b`. -/
noncomputable def pairProfile (a b : Fin M) (m : ℝ) : Fin M → ℝ :=
  fun i => (if i = a then 1 - m else 0) + (if i = b then m else 0)








end F1Tightness


