-- Prove2me | solution 1 for BookSixth.permanent_eq_card_matchings
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T02:38:57.874167+00:00
-- url     : https://prove2.me/submissions/1140e133-0e2a-4ece-a03a-eb3505177c92

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) :
    Matrix.permanent M = ((Finset.univ.filter
      (fun σ : Equiv.Perm (Fin n) => ∀ i, M i (σ i) = 1)).card : ℝ) := by
  classical
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      ∏ i, M i (σ i) =
        if ∀ i, M i (σ i) = 1 then (1 : ℝ) else 0 := by
    intro σ
    by_cases h : ∀ i, M i (σ i) = 1
    · rw [if_pos h]
      apply Finset.prod_eq_one
      intro i _
      exact h i
    · rw [if_neg h]
      push_neg at h
      obtain ⟨i, hi⟩ := h
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rcases h01 i (σ i) with h0 | h1
      · exact h0
      · exact absurd h1 hi
  have hpermT : Matrix.permanent M
      = ∑ σ : Equiv.Perm (Fin n), ∏ i, M (σ i) i := by
    rw [Matrix.permanent]
  have hinner : ∀ σ : Equiv.Perm (Fin n),
      (∏ i, M i (σ.symm i)) = ∏ i, M (σ i) i := by
    intro σ
    apply Finset.prod_bij (fun i _ => σ.symm i)
    · intro a _
      exact Finset.mem_univ _
    · intro a₁ _ a₂ _ h
      exact σ.symm.injective h
    · intro b _
      exact ⟨σ b, Finset.mem_univ _, by simp⟩
    · intro a _
      have hs : σ (σ.symm a) = a := by simp
      rw [hs]
  have houter : (∑ σ : Equiv.Perm (Fin n), ∏ i, M (σ i) i)
      = ∑ σ : Equiv.Perm (Fin n), ∏ i, M i (σ i) := by
    apply Finset.sum_bij (fun σ _ => σ.symm)
    · intro σ _
      exact Finset.mem_univ _
    · intro a₁ _ a₂ _ h
      rw [← Equiv.symm_symm a₁, ← Equiv.symm_symm a₂, h]
    · intro τ _
      exact ⟨τ.symm, Finset.mem_univ _, Equiv.symm_symm τ⟩
    · intro σ _
      exact (hinner σ).symm
  rw [hpermT, houter]
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_one]
