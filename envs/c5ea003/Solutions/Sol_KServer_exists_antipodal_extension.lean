-- Prove2me | solution 1 for KServer.exists_antipodal_extension
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T19:42:21.905536+00:00
-- url     : https://prove2.me/submissions/0e1735ae-5e74-43c7-9079-6b2c0a71bf9e

import Mathlib

/-- The distance function of the antipodal extension. -/
private noncomputable def antiD {M : Type} [MetricSpace M] (Δ : ℝ) :
    (M ⊕ M) → (M ⊕ M) → ℝ
  | Sum.inl x, Sum.inl y => dist x y
  | Sum.inr x, Sum.inr y => dist x y
  | Sum.inl x, Sum.inr y => 2 * Δ - dist x y
  | Sum.inr x, Sum.inl y => 2 * Δ - dist x y

/-- **Every metric space embeds isometrically into one in which every point has an
antipode.** -/
theorem solution (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ x y : M, dist x y ≤ Δ) :
    ∃ D : (M ⊕ M) → (M ⊕ M) → ℝ,
      (∀ p, D p p = 0)
      ∧ (∀ p q, D p q = D q p)
      ∧ (∀ p q r, D p r ≤ D p q + D q r)
      ∧ (∀ p q, D p q = 0 → p = q)
      ∧ (∀ x y : M, D (Sum.inl x) (Sum.inl y) = dist x y)
      ∧ (∀ p q : M ⊕ M, D p q + D q (Sum.swap p) = 2 * Δ) := by
  refine ⟨antiD Δ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (x | x) <;> simp [antiD]
  · rintro (x | x) (y | y) <;> simp [antiD, dist_comm]
  · rintro (x | x) (y | y) (z | z) <;>
      simp only [antiD] <;>
      [ exact dist_triangle x y z;
        linarith [dist_triangle y x z, dist_comm y x];
        linarith [hΔ x y, hΔ y z, hΔ x z];
        linarith [dist_triangle x z y, dist_comm z y];
        linarith [dist_triangle x z y, dist_comm z y];
        linarith [hΔ x y, hΔ y z, hΔ x z];
        linarith [dist_triangle y x z, dist_comm y x];
        exact dist_triangle x y z ]
  · rintro (x | x) (y | y) h <;> simp only [antiD] at h
    · rw [dist_eq_zero] at h; rw [h]
    · exfalso; have := hΔ x y; linarith
    · exfalso; have := hΔ x y; linarith
    · rw [dist_eq_zero] at h; rw [h]
  · intro x y; rfl
  · rintro (x | x) (y | y) <;> simp [antiD, Sum.swap, dist_comm] <;> ring
