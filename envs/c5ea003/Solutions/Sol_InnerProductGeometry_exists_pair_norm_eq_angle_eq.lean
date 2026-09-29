-- Prove2me | solution 1 for InnerProductGeometry.exists_pair_norm_eq_angle_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T00:52:55.281891+00:00
-- url     : https://prove2.me/submissions/72e6cfb9-55dc-4b78-b700-13692ecd5ff4

import Mathlib

open InnerProductGeometry

theorem solution (t s α : ℝ) (ht : 0 < t) (hs : 0 < s)
    (h0 : 0 ≤ α) (hpi : α ≤ Real.pi) :
    ∃ b c : ℂ, ‖b‖ = t ∧ ‖c‖ = s ∧ angle b c = α := by
  set c : ℂ := (↑(s * Real.cos α) : ℂ) + (↑(s * Real.sin α) : ℂ) * Complex.I with hcdef
  have hbn : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht]
  have hcn : ‖c‖ = s := by
    rw [hcdef, Complex.norm_add_mul_I]
    rw [show (s * Real.cos α) ^ 2 + (s * Real.sin α) ^ 2 = s ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq α]]
    exact Real.sqrt_sq hs.le
  have hip : (inner ℝ (t : ℂ) c : ℝ) = t * s * Real.cos α := by
    rw [Complex.inner, hcdef]
    simp only [Complex.conj_ofReal, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  refine ⟨(t : ℂ), c, hbn, hcn, ?_⟩
  unfold angle
  rw [hbn, hcn, hip]
  rw [show t * s * Real.cos α / (t * s) = Real.cos α by
    field_simp]
  exact Real.arccos_cos h0 hpi
