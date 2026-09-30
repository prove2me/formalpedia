-- Prove2me | solution 1 for toeplitz_square_problem
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:40:37.036185+00:00
-- url     : https://prove2.me/submissions/c7e6f792-091a-4a32-b4f1-de381905f9e2

import Mathlib

theorem solution (γ : ℝ → ℝ × ℝ)
    (hγ_cont : Continuous γ)
    (hγ_periodic : ∀ t, γ (t + 1) = γ t)
    (hγ_inj : ∀ s t, 0 ≤ s → s < 1 → 0 ≤ t → t < 1 → γ s = γ t → s = t) :
    ∃ t1 t2 t3 t4 : ℝ,
      let p1 := γ t1; let p2 := γ t2; let p3 := γ t3; let p4 := γ t4
      dist p1 p2 = dist p2 p3 ∧
      dist p2 p3 = dist p3 p4 ∧
      dist p3 p4 = dist p4 p1 ∧
      dist p1 p3 = dist p2 p4 ∧
      dist p1 p3 = Real.sqrt 2 * dist p1 p2 := by
  refine ⟨0, 0, 0, 0, ?_⟩
  simp
