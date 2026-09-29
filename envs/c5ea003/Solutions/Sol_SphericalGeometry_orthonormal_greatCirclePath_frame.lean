-- Prove2me | solution 1 for SphericalGeometry.orthonormal_greatCirclePath_frame
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T11:17:56.658643+00:00
-- url     : https://prove2.me/submissions/42e4a575-895b-443e-9f0c-3d878481b6bb

import Definitions.Def_spherical_great_circle

open SphericalGeometry

universe u

theorem solution {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (h12 : inner ℝ v1 v2 = (0:ℝ))
    (c : ℝ) :
    ‖greatCirclePath v1 v2 c‖ = 1 ∧ ‖greatCirclePath v2 (-v1) c‖ = 1
      ∧ inner ℝ (greatCirclePath v1 v2 c) (greatCirclePath v2 (-v1) c) = (0:ℝ) := by
  have hs1 : inner ℝ v1 v1 = (1:ℝ) := by
    rw [real_inner_self_eq_norm_sq, h1]; norm_num
  have hs2 : inner ℝ v2 v2 = (1:ℝ) := by
    rw [real_inner_self_eq_norm_sq, h2]; norm_num
  have h21 : inner ℝ v2 v1 = (0:ℝ) := by rw [real_inner_comm]; exact h12
  have hpyth : Real.cos c ^ 2 + Real.sin c ^ 2 = 1 := by
    rw [add_comm]; exact Real.sin_sq_add_cos_sq c
  refine ⟨?_, ?_, ?_⟩
  · have hsq : ‖greatCirclePath v1 v2 c‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, greatCirclePath]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hs1, hs2, h12, h21]
      nlinarith [hpyth]
    nlinarith [hsq, norm_nonneg (greatCirclePath v1 v2 c)]
  · have hsq : ‖greatCirclePath v2 (-v1) c‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, greatCirclePath]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, inner_neg_left, inner_neg_right, hs1, hs2, h12, h21]
      nlinarith [hpyth]
    nlinarith [hsq, norm_nonneg (greatCirclePath v2 (-v1) c)]
  · rw [greatCirclePath, greatCirclePath]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, inner_neg_left, inner_neg_right, hs1, hs2, h12, h21]
    ring
