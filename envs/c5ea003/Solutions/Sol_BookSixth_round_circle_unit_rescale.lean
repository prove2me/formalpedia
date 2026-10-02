-- Prove2me | solution 1 for BookSixth.round_circle_unit_rescale
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:10:41.621796+00:00
-- url     : https://prove2.me/submissions/fd4763aa-da80-474f-9f63-dca0b67e031d

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

theorem solution (c u v : Space3) (r : ℝ) (hr : 0 < r)
    (D : Set Space3)
    (hD : D = Set.range (fun t : ℝ => c + (r * Real.cos t) • u +
      (r * Real.sin t) • v)) :
    (fun x : Space3 => r ⁻¹ • (x - c) + c) '' D
      = Set.range (fun t : ℝ => c + (Real.cos t) • u + (Real.sin t) • v) := by
  rw [hD,←Set.range_comp]
  congr 1
  funext t
  ext i
  simp only [Function.comp_apply,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  field_simp [ne_of_gt hr]
  <;> ring
