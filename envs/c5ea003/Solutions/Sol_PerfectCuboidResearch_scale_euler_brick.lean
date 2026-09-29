-- Prove2me | solution 1 for PerfectCuboidResearch.scale_euler_brick
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:40:45.991692+00:00
-- url     : https://prove2.me/submissions/7d7a2808-2780-42d9-9eab-17f200ccfac7

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
theorem solution{x y z : ℕ} (k : ℕ)
    (h : IsEulerBrick x y z) : IsEulerBrick (k * x) (k * y) (k * z) := by
  rcases h with ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩
  refine ⟨⟨k * a, ?_⟩, ⟨k * b, ?_⟩, ⟨k * c, ?_⟩⟩
  · simp only [mul_pow]
    rw [ha]
    ring
  · simp only [mul_pow]
    rw [hb]
    ring
  · simp only [mul_pow]
    rw [hc]
    ring
