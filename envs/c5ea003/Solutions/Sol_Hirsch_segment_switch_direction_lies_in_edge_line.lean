-- Prove2me | solution 1 for Hirsch.segment_switch_direction_lies_in_edge_line
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-13T19:12:23.866517+00:00
-- url     : https://prove2.me/submissions/52c44fa2-0eca-422f-b937-69df5a00bb8f

import Mathlib

set_option autoImplicit false
noncomputable section

private theorem common_row_annihilates_switch
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (a : E →ₗ[ℝ] ℝ) (b τ : ℝ) (x y g : E) (hτ : 0 < τ)
    (hx : a x = b) (hy : a y = b)
    (hforward : a (x + τ • g) ≤ b)
    (hbackward : a (y - τ • g) ≤ b) : a g = 0 := by
  simp only [map_add, map_sub, map_smul, smul_eq_mul, hx, hy] at hforward hbackward
  nlinarith

theorem solution
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (τ : ℝ) (x y g : E) (hτ : 0 < τ)
    (hx : ∀ i, a i x = b i) (hy : ∀ i, a i y = b i)
    (hforward : ∀ i, a i (x + τ • g) ≤ b i)
    (hbackward : ∀ i, a i (y - τ • g) ≤ b i)
    (hkernel : ∀ z : E, (∀ i, a i z = 0) → ∃ r : ℝ, z = r • (y-x)) :
    ∃ r : ℝ, g = r • (y-x) := by
  apply hkernel g
  intro i
  exact common_row_annihilates_switch (a i) (b i) τ x y g hτ
    (hx i) (hy i) (hforward i) (hbackward i)

#print axioms solution
