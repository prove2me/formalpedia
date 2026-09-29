-- Prove2me | solution 1 for F1Tightness.deltaLast_meanPos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:25:28.316545+00:00
-- url     : https://prove2.me/submissions/1a40720f-bb67-4f48-8a90-876c6079c39b

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
theorem solution{M : ℕ} (hM : 0 < M) :
    meanPos (deltaLast M) = (2 * (M : ℝ) - 1) / (2 * (M : ℝ)) := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hcast : (((M - 1 : ℕ) : ℝ)) = (M : ℝ) - 1 := by
    have : ((M - 1 : ℕ) : ℝ) = ((M : ℕ) : ℝ) - ((1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.cast_sub hM
    simpa using this
  have h : ∀ i : Fin M,
      ((((i : ℕ) : ℝ) + 1 / 2) / (M : ℝ)) * deltaLast M i
        = if i = (⟨M - 1, by omega⟩ : Fin M) then (2 * (M : ℝ) - 1) / (2 * (M : ℝ)) else 0 := by
    intro i
    unfold deltaLast
    by_cases h0 : (i : ℕ) = M - 1
    · have hi : i = (⟨M - 1, by omega⟩ : Fin M) := by simp [Fin.ext_iff, h0]
      simp only [hi, if_true]
      rw [hcast]
      field_simp
      ring
    · have hi : i ≠ (⟨M - 1, by omega⟩ : Fin M) := by simp [Fin.ext_iff, h0]
      simp [h0, hi]
  rw [meanPos, Finset.sum_congr rfl fun i _ => h i]
  simp
