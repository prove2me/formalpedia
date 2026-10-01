-- Prove2me | solution 1 for Real.sub_eq_sub_of_cos_eq_cos_of_sin_eq_sin
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T13:54:09.428475+00:00
-- url     : https://prove2.me/submissions/f5493a0a-83a2-45dc-93ce-ba550360dfce

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Topology.Separation.Lemmas

set_option autoImplicit false

theorem solution {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {θ ψ : X → ℝ} (hθ : Continuous θ) (hψ : Continuous ψ)
    (hcos : ∀ x, Real.cos (θ x) = Real.cos (ψ x))
    (hsin : ∀ x, Real.sin (θ x) = Real.sin (ψ x)) (x y : X) :
    θ x - ψ x = θ y - ψ y := by
  have hsub : Set.range (fun z ↦ θ z - ψ z) ⊆ Set.range (fun n : ℤ ↦ 2 * Real.pi * n) := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨n, hn⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp
      (Real.Angle.cos_sin_inj (hcos z) (hsin z))
    exact ⟨n, hn.symm⟩
  have hconst := (Set.countable_range (fun n : ℤ ↦ 2 * Real.pi * n)).isTotallyDisconnected
    _ hsub (isPreconnected_range (hθ.sub hψ))
  exact hconst (Set.mem_range_self x) (Set.mem_range_self y)
