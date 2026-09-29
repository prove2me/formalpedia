-- Prove2me | solution 1 for F1Tightness.deltaLast_gapX
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:32:50.992369+00:00
-- url     : https://prove2.me/submissions/059770dc-d882-4e9b-94af-b822b3a95231

-- Sol generated from Probability/F1TightnessFibration.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessFibration
import Theorems.Thm_F1Tightness_deltaLast_meanPos
import Theorems.Thm_F1Tightness_gapX_eq_meanPos

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




theorem deltaLast_nonneg (M : ℕ) : ∀ i, 0 ≤ deltaLast M i := by
  intro i; unfold deltaLast; split <;> norm_num


theorem deltaLast_sum {M : ℕ} (hM : 0 < M) : ∑ i : Fin M, deltaLast M i = 1 := by
  have h : ∀ i : Fin M, deltaLast M i = if i = (⟨M - 1, by omega⟩ : Fin M) then 1 else 0 := by
    intro i
    unfold deltaLast
    congr 1
    simp [Fin.ext_iff]
  simp [h]







open F1Tightness in
theorem solution{M : ℕ} (hM : 0 < M) :
    gapX (deltaLast M) = ((M : ℝ) + 1) / (2 * (M : ℝ)) := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hden : 2 * (M : ℝ) * ((2 * (M : ℝ) - 1) / (2 * (M : ℝ))) + 1 = 2 * (M : ℝ) := by
    field_simp
    ring
  rw [gapX_eq_meanPos hM (deltaLast_nonneg M) (deltaLast_sum hM), deltaLast_meanPos hM, hden]
