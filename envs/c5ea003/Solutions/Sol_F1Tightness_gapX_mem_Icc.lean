-- Prove2me | solution 1 for F1Tightness.gapX_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:40:45.862304+00:00
-- url     : https://prove2.me/submissions/2183a463-d52a-4969-9e46-490768eb9fd9

-- Sol generated from Probability/F1TightnessFibration.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessFibration
import Theorems.Thm_F1Tightness_gapX_eq_meanPos
import Theorems.Thm_F1Tightness_meanPos_mem_Icc

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
    ((M : ℝ) + 1) / (2 * (M : ℝ)) ≤ gapX p ∧ gapX p ≤ ((M : ℝ) + 1) / 2 := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  obtain ⟨hlow, hhigh⟩ := meanPos_mem_Icc hM hp hsum
  have hE0 : 0 < meanPos p := lt_of_lt_of_le (by positivity) hlow
  have hden : 0 < 2 * (M : ℝ) * meanPos p + 1 := by positivity
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (M : ℝ))] at hhigh
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * (M : ℝ))] at hlow
  rw [gapX_eq_meanPos hM hp hsum]
  constructor
  · rw [div_le_div_iff₀ (by positivity) hden]
    nlinarith
  · rw [div_le_div_iff₀ hden (by norm_num)]
    nlinarith
