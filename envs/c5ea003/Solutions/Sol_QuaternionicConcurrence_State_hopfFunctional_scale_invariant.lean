-- Prove2me | solution 1 for QuaternionicConcurrence.State.hopfFunctional_scale_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T17:41:10.233225+00:00
-- url     : https://prove2.me/submissions/f0c87321-d8af-489b-8293-e1f63dd6a679

import Mathlib
import Definitions.Def_Geometry_QuaternionicConcurrence
open Complex ComplexConjugate QuaternionicConcurrence QuaternionicConcurrence.State in
theorem solution (ψ : State) (z : ℂ) (hz : z ≠ 0) :
    hopfFunctional ⟨z * ψ.a, z * ψ.b, z * ψ.c, z * ψ.d⟩ =
      hopfFunctional ψ := by
  -- the squared norm scales by `|z|²`, the determinant by `z²`
  have hn : QuaternionicConcurrence.State.normSq ⟨z * ψ.a, z * ψ.b, z * ψ.c, z * ψ.d⟩
      = Complex.normSq z * ψ.normSq := by
    simp only [QuaternionicConcurrence.State.normSq, map_mul]
    ring
  have hd : QuaternionicConcurrence.State.determinant ⟨z * ψ.a, z * ψ.b, z * ψ.c, z * ψ.d⟩
      = z ^ 2 * ψ.determinant := by
    simp only [QuaternionicConcurrence.State.determinant]
    ring
  have hz2 : 0 < Complex.normSq z := Complex.normSq_pos.2 hz
  unfold hopfFunctional
  rw [hn, hd, norm_mul, norm_pow, ← Complex.normSq_eq_norm_sq]
  by_cases h0 : ψ.normSq = 0
  · simp [h0]
  · rw [if_neg (mul_ne_zero hz2.ne' h0), if_neg h0, mul_left_comm,
      mul_div_mul_left _ _ hz2.ne']
