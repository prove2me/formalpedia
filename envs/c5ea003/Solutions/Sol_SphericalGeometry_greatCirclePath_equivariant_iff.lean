-- Prove2me | solution 1 for SphericalGeometry.greatCirclePath_equivariant_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T11:25:09.007625+00:00
-- url     : https://prove2.me/submissions/d5c00245-30ec-436a-8865-04d53d3898d9

import Theorems.Thm_SphericalGeometry_greatCirclePath_add
import Theorems.Thm_SphericalGeometry_greatCirclePath_comp_linearIsometryEquiv

open SphericalGeometry

universe u

theorem solution {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : E ≃ₗᵢ[ℝ] E) (v1 v2 : E) (T : ℝ) :
    (∀ s : ℝ, greatCirclePath v1 v2 (s + T) = w (greatCirclePath v1 v2 s))
      ↔ (w v1 = greatCirclePath v1 v2 T ∧ w v2 = greatCirclePath v2 (-v1) T) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 := h 0
      rw [zero_add] at h0
      have hg0 : greatCirclePath v1 v2 (0:ℝ) = v1 := by
        simp [greatCirclePath]
      rw [hg0] at h0
      exact h0.symm
    · have h1 := h (Real.pi / 2)
      rw [SphericalGeometry.greatCirclePath_add] at h1
      have hgh : greatCirclePath v1 v2 (Real.pi / 2) = v2 := by
        simp [greatCirclePath]
      rw [hgh] at h1
      have hlhs : greatCirclePath (greatCirclePath v1 v2 T)
          (greatCirclePath v2 (-v1) T) (Real.pi / 2)
          = greatCirclePath v2 (-v1) T := by
        simp [greatCirclePath]
      rw [hlhs] at h1
      exact h1.symm
  · rintro ⟨hw1, hw2⟩ s
    rw [SphericalGeometry.greatCirclePath_add,
      SphericalGeometry.greatCirclePath_comp_linearIsometryEquiv, hw1, hw2]
