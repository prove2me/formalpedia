-- Prove2me | solution 1 for BookSixth.orthonormal_frame_cross_unit_euclidean_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T03:44:45.379846+00:00
-- url     : https://prove2.me/submissions/66bf34d6-106f-44cc-9fd6-f08e577ed0b1

import Mathlib
import Definitions.Def_BookSixth
import Mathlib.LinearAlgebra.CrossProduct
open scoped BigOperators
open BookSixth
open Matrix

/-- **The cross product of an orthonormal frame is a Euclidean unit normal.**

For an orthonormal pair `u`, `v` in `Space3 = Fin 3 → ℝ` — in the sense used by
`RoundCircle`, so `(∑ i, u i * u i) = 1` and friends — the vector
`w := u ⨯₃ v` has Euclidean length one and is perpendicular to both.

The norm is the genuine Euclidean one. `Space3` carries the supremum norm, in
which any vector with a coordinate `±1` already has norm one, so the
`RoundCircle` conditions are the square of the Euclidean norm rather than the
supremum norm. The conclusion `(∑ i, w i * w i) = 1` is exactly `‖w‖₂ ^ 2 = 1`.

Orthonormality of the pair forces the length to be *equal* to one, not merely at
most one: this is Lagrange's identity `‖u × v‖₂ ^ 2 = ‖u‖₂^2 ‖v‖₂^2 - (u · v)^2`.

This is the normal required to write the plane of a round circle as
`{x : (x - c) ⬝ᵥ w = 0}` in the lifted-dome construction underlying the
collision-free shrinking argument. -/
theorem solution (u v : Space3) (hu : (∑ i, u i * u i) = 1)
    (hv : (∑ i, v i * v i) = 1) (huv : (∑ i, u i * v i) = 0) :
    (∑ i, (u ⨯₃ v) i * (u ⨯₃ v) i) = 1 ∧
      (∑ i, (u ⨯₃ v) i * u i) = 0 ∧
      (∑ i, (u ⨯₃ v) i * v i) = 0 := by
  have hlen : (∑ i, (u ⨯₃ v) i * (u ⨯₃ v) i) = 1 := by
    have h := cross_dot_cross u v u v
    have hvu : (∑ i, v i * u i) = 0 := by
      simpa [Finset.sum_comm, mul_comm] using huv
    rw [dotProduct, dotProduct, dotProduct, dotProduct, dotProduct] at h
    rw [hu, hv, huv, hvu] at h
    norm_num at h
    exact h
  have hperp_u : (∑ i, (u ⨯₃ v) i * u i) = 0 := by
    have h : u ⬝ᵥ (u ⨯₃ v) = 0 := dot_self_cross u v
    simpa [dotProduct, Finset.sum_comm, mul_comm] using h
  have hperp_v : (∑ i, (u ⨯₃ v) i * v i) = 0 := by
    have h : v ⬝ᵥ u ⨯₃ v = 0 := dot_cross_self u v
    simpa [dotProduct, Finset.sum_comm, mul_comm] using h
  exact ⟨hlen, hperp_u, hperp_v⟩
