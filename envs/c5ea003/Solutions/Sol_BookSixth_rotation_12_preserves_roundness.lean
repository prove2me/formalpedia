-- Prove2me | solution 1 for BookSixth.rotation_12_preserves_roundness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T17:46:58.625361+00:00
-- url     : https://prove2.me/submissions/296adb9f-daf9-4b97-8720-1cb2efdfb417

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

/-- A rotation in the plane of coordinates 1 and 2 sends a round circle to a round
circle: the centre becomes `R c`, the orthonormal frame becomes `R u`, `R v`, and the
radius is unchanged. The three orthonormal equations follow from
`Real.cos_sq_add_sin_sq`; the mixed coordinates 1 and 2 make the algebra a direct
transcription of the 0-1 case with indices permuted. -/
theorem solution (C : Set Space3) (θ : ℝ) (hC : RoundCircle C) :
    RoundCircle
      ((fun x : Space3 => ![x 0, Real.cos θ * x 1 - Real.sin θ * x 2,
          Real.sin θ * x 1 + Real.cos θ * x 2]) '' C) := by
  obtain ⟨c, u, v, r, hr, hu, hv, huv, hCeq⟩ := hC
  simp only [Fin.sum_univ_three] at hu hv huv
  refine ⟨![c 0, Real.cos θ * c 1 - Real.sin θ * c 2,
      Real.sin θ * c 1 + Real.cos θ * c 2],
    ![u 0, Real.cos θ * u 1 - Real.sin θ * u 2,
        Real.sin θ * u 1 + Real.cos θ * u 2],
    ![v 0, Real.cos θ * v 1 - Real.sin θ * v 2,
        Real.sin θ * v 1 + Real.cos θ * v 2],
    r, hr, ?_, ?_, ?_, ?_⟩
  · have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    linear_combination hu + (u 1 ^ 2 + u 2 ^ 2) * hcs
  · have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    linear_combination hv + (v 1 ^ 2 + v 2 ^ 2) * hcs
  · have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    linear_combination huv + (u 1 * v 1 + u 2 * v 2) * hcs
  · rw [hCeq, ← Set.range_comp']
    congr 1
    funext t
    funext i
    fin_cases i <;>
      simp [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_add, smul_smul] <;>
      ring
