-- Prove2me | solution 1 for arnold_conjecture_torus
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:27:23.280718+00:00
-- url     : https://prove2.me/submissions/a234cf12-90c1-4f3b-b48d-554ba7db47e1

import Mathlib

theorem solution (n : ℕ) (hn : 1 ≤ n)
    (phi : (Fin n → AddCircle (1 : ℝ)) → (Fin n → AddCircle (1 : ℝ)))
    (hphi : Continuous phi)
    (hhom : ∀ x y : Fin n → AddCircle (1 : ℝ),
      phi (x + y) = phi x + phi y) :
    ∃ x : Fin n → AddCircle (1 : ℝ), phi x = x := by
  refine ⟨0, ?_⟩
  have h := hhom 0 0
  rw [add_zero] at h
  simpa using h
