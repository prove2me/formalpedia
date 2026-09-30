-- Prove2me | solution 1 for polynomial_freiman_ruzsa
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:12:22.902712+00:00
-- url     : https://prove2.me/submissions/33ad1bfe-f194-441d-8c4e-0cfdf1173cec

import Mathlib

theorem solution (A : Finset ℤ)
    (K : ℝ) (hK : 1 ≤ K)
    (hA : ((A.image₂ (· + ·) A).card : ℝ) ≤ K * A.card) :
    ∃ (P H : Finset ℤ),
      (H.card : ℝ) ≤ K ^ 12 * A.card ∧
      A ⊆ H.image₂ (· + ·) P := by
  refine ⟨{0}, A, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ K ^ 12 := one_le_pow₀ hK
    have h2 : (0 : ℝ) ≤ A.card := by positivity
    nlinarith
  · intro a ha
    rw [Finset.mem_image₂]
    exact ⟨a, ha, 0, Finset.mem_singleton_self 0, add_zero a⟩
