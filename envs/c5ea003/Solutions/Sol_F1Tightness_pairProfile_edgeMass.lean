-- Prove2me | solution 1 for F1Tightness.pairProfile_edgeMass
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:40:46.426171+00:00
-- url     : https://prove2.me/submissions/5e8e233f-c89d-4b8b-b00c-cd78b41f8249

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
theorem solution{K : ℕ} {a b : Fin M} {m : ℝ}
    (ha : (a : ℕ) < K) (hb : K ≤ (b : ℕ)) :
    edgeMass K (pairProfile a b m) = m := by
  have hane : ∀ i ∈ Finset.univ.filter (fun i : Fin M => K ≤ (i : ℕ)), i ≠ a := by
    intro i hi hia
    have : K ≤ (i : ℕ) := by simpa using hi
    rw [hia] at this
    omega
  unfold edgeMass pairProfile
  rw [Finset.sum_add_distrib]
  have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin M => K ≤ (i : ℕ)),
      (if i = a then 1 - m else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp [hane i hi]
  have h2 : ∑ i ∈ Finset.univ.filter (fun i : Fin M => K ≤ (i : ℕ)),
      (if i = b then m else 0) = m := by
    rw [Finset.sum_ite_eq' _ b]
    simp [hb]
  rw [h1, h2, zero_add]
