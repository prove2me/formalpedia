-- Prove2me | solution 1 for VectorSpaceOpt.bounded_iff_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:47:53.389291+00:00
-- url     : https://prove2.me/submissions/bc4f7b34-6629-457c-aa5b-1c368f34e16f

import Mathlib


theorem solution {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X →ₗ[ℝ] ℝ) :
    (∃ M : ℝ, ∀ x : X, |f x| ≤ M * ‖x‖) ↔ Continuous f := by
  constructor
  · rintro ⟨M, hM⟩
    exact (f.mkContinuous M (fun x => by simpa [Real.norm_eq_abs] using hM x)).continuous
  · intro hc
    let F : X →L[ℝ] ℝ := ⟨f, hc⟩
    exact ⟨‖F‖, fun x => by simpa [Real.norm_eq_abs] using F.le_opNorm x⟩
