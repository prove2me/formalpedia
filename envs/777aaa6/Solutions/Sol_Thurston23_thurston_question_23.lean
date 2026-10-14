-- Prove2me | solution 1 for Thurston23.thurston_question_23
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-11T20:19:13.523599+00:00
-- url     : https://prove2.me/submissions/f7efc007-a9b6-449f-8ba7-90291c3e9170
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Thurston23_bundle
import Theorems.Thm_Thurston23_exists_hyperbolicVolume_rat_mul_catalan
import Theorems.Thm_Thurston23_exists_hyperbolicVolume_rat_mul_LChiMinusThree
import Theorems.Thm_catalan_ne_rat_mul_sqrt_three_LChiMinusThree

open Thurston23

/-- Thurston's Question 23, reduced to the two Bianchi volume identities and the
irrationality of the ratio of the two `L`-values. -/
theorem solution :
    ∃ v ∈ hyperbolicVolumes, ∃ w ∈ hyperbolicVolumes,
      ∀ q : ℚ, v ≠ (q : ℝ) * w := by
  obtain ⟨v, hv, a, ha, hveq⟩ := exists_hyperbolicVolume_rat_mul_catalan
  obtain ⟨w, hw, b, -, hweq⟩ := exists_hyperbolicVolume_rat_mul_LChiMinusThree
  refine ⟨v, hv, w, hw, fun q hq => ?_⟩
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  refine catalan_ne_rat_mul_sqrt_three_LChiMinusThree (q * b / a) ?_
  rw [hveq, hweq] at hq
  push_cast
  field_simp
  field_simp at hq
  linarith [hq]
