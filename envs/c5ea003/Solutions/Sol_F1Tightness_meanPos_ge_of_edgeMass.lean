-- Prove2me | solution 1 for F1Tightness.meanPos_ge_of_edgeMass
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:35:50.580923+00:00
-- url     : https://prove2.me/submissions/5df1a7ad-8ef5-4a67-b098-09c64a9fcf9e

-- Sol generated from Probability/F1TightnessPolytope.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessFibration
import Definitions.Def_Probability_F1TightnessPolytope
import Theorems.Thm_F1Tightness_meanPos_eq_half_add

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
theorem solution{K : ℕ} {m : ℝ} {p : Fin M → ℝ} (hM : 0 < M)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i : Fin M, p i = 1) (hm : m ≤ edgeMass K p) :
    (1 / 2 + (K : ℝ) * m) / (M : ℝ) ≤ meanPos p := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  set S : Finset (Fin M) := Finset.univ.filter (fun i : Fin M => K ≤ (i : ℕ)) with hS
  have hsub : ∑ i ∈ S, (((i : ℕ) : ℝ) / (M : ℝ)) * p i
      ≤ ∑ i : Fin M, (((i : ℕ) : ℝ) / (M : ℝ)) * p i := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) ?_
    intro i _ _
    have := hp i
    positivity
  have hterm : ∀ i ∈ S, ((K : ℝ) / (M : ℝ)) * p i ≤ (((i : ℕ) : ℝ) / (M : ℝ)) * p i := by
    intro i hi
    have hKi : (K : ℝ) ≤ ((i : ℕ) : ℝ) := by
      have : K ≤ (i : ℕ) := by
        simpa [hS] using hi
      exact_mod_cast this
    have hdiv : (K : ℝ) / (M : ℝ) ≤ ((i : ℕ) : ℝ) / (M : ℝ) := by gcongr
    nlinarith [hp i]
  have hlow : ((K : ℝ) / (M : ℝ)) * edgeMass K p
      ≤ ∑ i ∈ S, (((i : ℕ) : ℝ) / (M : ℝ)) * p i := by
    rw [edgeMass, ← hS, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hKm : ((K : ℝ) / (M : ℝ)) * m ≤ ((K : ℝ) / (M : ℝ)) * edgeMass K p := by
    have hK0 : (0 : ℝ) ≤ (K : ℝ) / (M : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hm hK0
  have hmean := meanPos_eq_half_add (p := p) hM hsum
  have hsplit : (1 / 2 + (K : ℝ) * m) / (M : ℝ)
      = 1 / (2 * (M : ℝ)) + ((K : ℝ) / (M : ℝ)) * m := by
    field_simp
  rw [hsplit, hmean]
  linarith
