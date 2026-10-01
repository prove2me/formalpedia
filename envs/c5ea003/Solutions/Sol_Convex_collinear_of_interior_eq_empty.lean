-- Prove2me | solution 1 for Convex.collinear_of_interior_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T17:20:21.498469+00:00
-- url     : https://prove2.me/submissions/5fc09c50-0c71-49fb-9ef3-e72d2e3e03a8

import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Module

theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : Convex ℝ s) (hdim : finrank ℝ E ≤ 2)
    (hint : interior s = ∅) : Collinear ℝ s := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact collinear_empty ℝ E
  have hspan : vectorSpan ℝ s ≠ ⊤ := by
    intro h
    have ha : affineSpan ℝ s = ⊤ :=
      (AffineSubspace.direction_eq_top_iff_of_nonempty
        (hne.mono (subset_affineSpan ℝ s))).mp (by simpa only [direction_affineSpan] using h)
    have hi := hs.interior_nonempty_iff_affineSpan_eq_top.mpr ha
    simp [hint] at hi
  apply collinear_iff_finrank_le_one.mpr
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hspan)
  simp only [finrank_top] at hlt
  omega
