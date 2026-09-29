-- Prove2me | solution 1 for PerfectCuboidResearch.quadric_parametrization_complete
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:40:45.373868+00:00
-- url     : https://prove2.me/submissions/0865329a-567f-406f-8c41-27fa1cb325b6

-- Sol generated from Geometry/PerfectCuboid/AlgebraicSurface.lean
import Mathlib
import Definitions.Def_Geometry_PerfectCuboid_AlgebraicSurface
/-
# Perfect cuboids: an Euler brick near-miss and its algebraic surface

This file gives a self-contained formalization of Euler bricks and perfect
cuboids.  It verifies the classical brick `(44,117,240)`, proves that its space
diagonal is not integral, derives the diagonal-cone equation, and gives a
rational parametrization of the quadric underlying the normalized equations.
-/

open PerfectCuboidResearch
















open PerfectCuboidResearch in
theorem solution    {u v w : ℚ} (hquad : OnCuboidQuadric u v w) (hu : u ≠ 1) :
    let p := v / (u - 1)
    let q := w / (u - 1)
    1 + p ^ 2 - q ^ 2 ≠ 0 ∧
      u = (p ^ 2 - q ^ 2 - 1) / (1 + p ^ 2 - q ^ 2) ∧
      v = (-2 * p) / (1 + p ^ 2 - q ^ 2) ∧
      w = (-2 * q) / (1 + p ^ 2 - q ^ 2) := by
  dsimp
  unfold OnCuboidQuadric at hquad
  have hsub : u - 1 ≠ 0 := sub_ne_zero.mpr hu
  have hD : 1 + (v / (u - 1)) ^ 2 - (w / (u - 1)) ^ 2 =
      -2 / (u - 1) := by
    field_simp [hsub]
    nlinarith
  have hden : 1 + (v / (u - 1)) ^ 2 - (w / (u - 1)) ^ 2 ≠ 0 := by
    rw [hD]
    exact div_ne_zero (by norm_num) hsub
  have hN : (v / (u - 1)) ^ 2 - (w / (u - 1)) ^ 2 - 1 =
      (-2 * u) / (u - 1) := by
    field_simp [hsub]
    nlinarith
  refine ⟨hden, ?_⟩
  rw [hD, hN]
  constructor
  · field_simp [hsub]
  constructor
  · field_simp [hsub]
  · field_simp [hsub]
