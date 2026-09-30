-- Prove2me | solution 1 for Hirsch.positive_weighted_support_equals_common_tight_face
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-13T19:13:45.600034+00:00
-- url     : https://prove2.me/submissions/390eb741-4bea-494f-89ff-0df81cf71820

import Mathlib

open Set
open scoped BigOperators
set_option autoImplicit false
noncomputable section

private theorem weighted_support_eq_iff
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι]
    (P : Set E) (a : ι → E →ₗ[ℝ] ℝ) (b w : ι → ℝ)
    (hw : ∀ i, 0 < w i)
    (hb : ∀ i, ∀ x ∈ P, a i x ≤ b i)
    (x : E) (hx : x ∈ P) :
    (∑ i, w i * a i x) = (∑ i, w i * b i) ↔ ∀ i, a i x = b i := by
  classical
  constructor
  · intro he i
    by_contra hn
    have hi : a i x < b i := lt_of_le_of_ne (hb i x hx) hn
    have hs : (∑ j, w j * a j x) < ∑ j, w j * b j := by
      apply Finset.sum_lt_sum
      · intro j _
        exact mul_le_mul_of_nonneg_left (hb j x hx) (hw j).le
      · exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (hw i)⟩
    linarith
  · intro h
    exact Finset.sum_congr rfl (fun i _ => by rw [h i])

theorem solution
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι]
    (P : Set E) (a : ι → E →ₗ[ℝ] ℝ) (b w : ι → ℝ)
    (hw : ∀ i, 0 < w i)
    (hb : ∀ i, ∀ x ∈ P, a i x ≤ b i) :
    {x : E | x ∈ P ∧ (∑ i, w i * a i x) = (∑ i, w i * b i)} =
      {x : E | x ∈ P ∧ ∀ i, a i x = b i} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, he⟩
    exact ⟨hx, (weighted_support_eq_iff P a b w hw hb x hx).mp he⟩
  · rintro ⟨hx, he⟩
    exact ⟨hx, (weighted_support_eq_iff P a b w hw hb x hx).mpr he⟩

#print axioms solution
