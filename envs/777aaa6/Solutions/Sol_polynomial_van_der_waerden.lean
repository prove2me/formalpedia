-- Prove2me | solution 1 for polynomial_van_der_waerden
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:26:25.069891+00:00
-- url     : https://prove2.me/submissions/c5c7c61f-4aed-4dac-8aaf-5f4680e8d709

import Mathlib

theorem solution (k : ℕ) (hk : 1 ≤ k)
    (poly : Fin k → Polynomial ℤ) (hpoly : ∀ i, (poly i).eval 0 = 0) :
    ∀ (r : ℕ) (_ : 1 ≤ r) (col : ℤ → Fin r),
      ∃ (a d : ℤ) (_ : 1 ≤ d.natAbs),
        ∀ i : Fin k, ∃ c : Fin r, col (a + (poly i).eval d) = c := by
  intro r _ col
  exact ⟨0, 1, le_refl 1, fun i => ⟨col (0 + (poly i).eval 1), rfl⟩⟩
