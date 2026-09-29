-- Prove2me | solution 1 for F1Tightness.meanPos_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:38:27.149491+00:00
-- url     : https://prove2.me/submissions/3ccfa625-baf9-4d40-9c65-d8defedb7aef

-- Sol generated from Probability/F1TightnessFibration.lean
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













open F1Tightness in
theorem solution{p : Fin M → ℝ} (hM : 0 < M) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i : Fin M, p i = 1) :
    1 / (2 * (M : ℝ)) ≤ meanPos p ∧ meanPos p ≤ (2 * (M : ℝ) - 1) / (2 * (M : ℝ)) := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  constructor
  · have hlow : ∑ i : Fin M, (1 / (2 * (M : ℝ))) * p i ≤ meanPos p := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hi : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
      have : 1 / (2 * (M : ℝ)) ≤ (((i : ℕ) : ℝ) + 1 / 2) / (M : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) hMR]
        nlinarith
      exact mul_le_mul_of_nonneg_right this (hp i)
    rwa [← Finset.mul_sum, hsum, mul_one] at hlow
  · have hhigh : meanPos p ≤ ∑ i : Fin M, ((2 * (M : ℝ) - 1) / (2 * (M : ℝ))) * p i := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hi : ((i : ℕ) : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast i.isLt
      have : (((i : ℕ) : ℝ) + 1 / 2) / (M : ℝ) ≤ (2 * (M : ℝ) - 1) / (2 * (M : ℝ)) := by
        rw [div_le_div_iff₀ hMR (by positivity)]
        nlinarith
      exact mul_le_mul_of_nonneg_right this (hp i)
    rwa [← Finset.mul_sum, hsum, mul_one] at hhigh
