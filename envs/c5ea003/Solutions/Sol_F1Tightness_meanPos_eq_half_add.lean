-- Prove2me | solution 1 for F1Tightness.meanPos_eq_half_add
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:32:51.562957+00:00
-- url     : https://prove2.me/submissions/6154f41b-116c-435f-81b0-f73436ea22ec

-- Sol generated from Probability/F1TightnessPolytope.lean
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





/-! ## Attainment by a two-cell profile -/










open F1Tightness in
theorem solution{p : Fin M → ℝ} (hM : 0 < M)
    (hsum : ∑ i : Fin M, p i = 1) :
    meanPos p = 1 / (2 * (M : ℝ)) + ∑ i : Fin M, (((i : ℕ) : ℝ) / (M : ℝ)) * p i := by
  have hMR : (M : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    exact this.ne'
  have h : ∀ i : Fin M, ((((i : ℕ) : ℝ) + 1 / 2) / (M : ℝ)) * p i
      = (1 / (2 * (M : ℝ))) * p i + (((i : ℕ) : ℝ) / (M : ℝ)) * p i := by
    intro i
    field_simp
    ring
  rw [meanPos, Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib,
    ← Finset.mul_sum, hsum]
  ring
