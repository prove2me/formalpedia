-- Prove2me | solution 1 for EuclideanSpace.isBounded_coordinate_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T15:01:11.32087+00:00
-- url     : https://prove2.me/submissions/77ca44e1-17b6-4ff1-bb42-d4c7ad6309da

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

theorem solution (l r a b : ℝ) :
    Bornology.IsBounded {p : EuclideanSpace ℝ (Fin 2) | l ≤ p 0 ∧ p 0 ≤ r ∧ a ≤ p 1 ∧ p 1 ≤ b} := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(|l| + |r|) + (|a| + |b|), ?_⟩
  rintro p ⟨hl, hr, ha, hb⟩
  have hx : |p 0| ≤ |l| + |r| := abs_le.mpr
    ⟨by linarith [neg_abs_le l, abs_nonneg r],
      by linarith [le_abs_self r, abs_nonneg l]⟩
  have hy : |p 1| ≤ |a| + |b| := abs_le.mpr
    ⟨by linarith [neg_abs_le a, abs_nonneg b],
      by linarith [le_abs_self b, abs_nonneg a]⟩
  have hx2 := (sq_le_sq₀ (abs_nonneg (p 0)) (by positivity)).mpr hx
  have hy2 := (sq_le_sq₀ (abs_nonneg (p 1)) (by positivity)).mpr hy
  have hn := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn hx2 hy2
  nlinarith [mul_nonneg (by positivity : 0 ≤ |l| + |r|)
    (by positivity : 0 ≤ |a| + |b|), norm_nonneg p,
    abs_nonneg l, abs_nonneg r, abs_nonneg a, abs_nonneg b]
