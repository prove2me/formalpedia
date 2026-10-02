-- Prove2me | solution 1 for BookSixth.rotation_01_preserves_roundness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T17:47:33.984985+00:00
-- url     : https://prove2.me/submissions/85052a65-d0cf-4f52-a110-416b7acea06f

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

/-- A rotation of the first two coordinates sends a round circle to a round circle.
The new centre is `R c` and the new orthonormal frame is `R u`, `R v`, with the same
radius. Rotation is a similarity with scale 1, but unlike a uniform scaling it mixes
`u` and `v`, so the three orthonormal equations are re-verified from
`Real.cos_sq_add_sin_sq` rather than inherited. -/
theorem solution (C : Set Space3) (θ : ℝ) (hC : RoundCircle C) :
    RoundCircle
      ((fun x : Space3 => ![Real.cos θ * x 0 - Real.sin θ * x 1,
          Real.sin θ * x 0 + Real.cos θ * x 1, x 2]) '' C) := by
  obtain ⟨c, u, v, r, hr, hu, hv, huv, hCeq⟩ := hC
  simp only [Fin.sum_univ_three] at hu hv huv
  refine ⟨![Real.cos θ * c 0 - Real.sin θ * c 1,
      Real.sin θ * c 0 + Real.cos θ * c 1, c 2],
    ![Real.cos θ * u 0 - Real.sin θ * u 1,
        Real.sin θ * u 0 + Real.cos θ * u 1, u 2],
    ![Real.cos θ * v 0 - Real.sin θ * v 1,
        Real.sin θ * v 0 + Real.cos θ * v 1, v 2],
    r, hr, ?_, ?_, ?_, ?_⟩
  · have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    linear_combination hu + (u 0 ^ 2 + u 1 ^ 2) * hcs
  · have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    linear_combination hv + (v 0 ^ 2 + v 1 ^ 2) * hcs
  · have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    linear_combination huv + (u 0 * v 0 + u 1 * v 1) * hcs
  · rw [hCeq, ← Set.range_comp]
    congr 1
    funext t
    funext i
    fin_cases i <;>
      simp [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_add, smul_smul] <;>
      ring
