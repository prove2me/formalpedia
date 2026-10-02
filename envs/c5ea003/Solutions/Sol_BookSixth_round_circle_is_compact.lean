-- Prove2me | solution 1 for BookSixth.round_circle_is_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-26T19:55:47.882028+00:00
-- url     : https://prove2.me/submissions/7ae3719a-ef39-4a69-851b-fb282052d36a

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem solution {C : Set Space3} (hC : RoundCircle C) : IsCompact C := by
  obtain ⟨c, u, v, r, hr, _, _, _, hCrange⟩ := hC
  have hper : Function.Periodic (fun t : ℝ => c + (r * Real.cos t) • u
      + (r * Real.sin t) • v) (2 * Real.pi) := by
    intro t
    have hc : Real.cos (t + 2 * Real.pi) = Real.cos t := Real.cos_add_two_pi t
    have hs : Real.sin (t + 2 * Real.pi) = Real.sin t := Real.sin_add_two_pi t
    simp only [hc, hs, add_zero]
  have hIcc : (fun t : ℝ => c + (r * Real.cos t) • u + (r * Real.sin t) • v)
      '' Set.Icc (0 : ℝ) (0 + 2 * Real.pi)
      = Set.range (fun t : ℝ => c + (r * Real.cos t) • u + (r * Real.sin t) • v) :=
    hper.image_Icc (by positivity) 0
  rw [hCrange, ← hIcc]
  have hcont : Continuous (fun t : ℝ => c + (r * Real.cos t) • u
      + (r * Real.sin t) • v) :=
    (continuous_const.add ((continuous_const.mul Real.continuous_cos).smul
      continuous_const)).add
      ((continuous_const.mul Real.continuous_sin).smul continuous_const)
  exact IsCompact.image isCompact_Icc hcont
