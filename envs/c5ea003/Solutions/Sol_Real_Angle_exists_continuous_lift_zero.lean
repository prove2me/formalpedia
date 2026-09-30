-- Prove2me | solution 1 for Real.Angle.exists_continuous_lift_zero
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-29T23:24:35.604811+00:00
-- url     : https://prove2.me/submissions/593a6c80-1b89-4ad6-8dd8-8aeac41044d0

import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

set_option autoImplicit false

open scoped unitInterval

theorem solution (θ : I → Real.Angle) (hθ : Continuous θ)
    (hzero : θ 0 = 0) :
    ∃ α : I → ℝ, Continuous α ∧ α 0 = 0 ∧ ∀ t, (α t : Real.Angle) = θ t := by
  have hcov : IsCoveringMap ((↑) : ℝ → Real.Angle) := AddCircle.isCoveringMap_coe (2 * Real.pi)
  obtain ⟨α, hα, hα0⟩ := hcov.exists_path_lifts
    (⟨θ, hθ⟩ : C(I, Real.Angle)) (0 : ℝ) (by simpa using hzero)
  exact ⟨α, α.continuous, hα0, fun t ↦ congrFun hα t⟩
