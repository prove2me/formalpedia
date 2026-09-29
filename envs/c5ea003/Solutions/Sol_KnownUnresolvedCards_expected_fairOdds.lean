-- Prove2me | solution 1 for KnownUnresolvedCards.expected_fairOdds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T21:33:43.930579+00:00
-- url     : https://prove2.me/submissions/2b025ff5-f235-43c5-bf68-14ee765095b7

import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
import Definitions.Def_MachineLearning_KnownUnresolvedCards_DeckGame
import Definitions.Def_MachineLearning_KnownUnresolvedCards_PermCount
open KnownUnresolvedCards in
theorem solution {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] (g : α → α) :
    E (deckScore ((Fintype.card α : ℚ) - 1) (-1) g) = 0 := by
  have hslot : ∀ (w l : ℚ) (i a : α), E (slotScore w l i a) = (w - l) / (Fintype.card α : ℚ) + l := by
    intro w l i a
    have hfib : ∀ (i a : α), ((Finset.univ.filter (fun σ : Equiv.Perm α => σ i = a)).card : ℚ)
        = (Fintype.card (Equiv.Perm α) : ℚ) / Fintype.card α := by
      intro i a
      have heq : ∀ b, (Finset.univ.filter (fun σ : Equiv.Perm α => σ i = b)).card
          = (Finset.univ.filter (fun σ : Equiv.Perm α => σ i = a)).card := by
        intro b
        apply Finset.card_bij (fun σ _ => Equiv.swap a b * σ)
        · intro σ hσ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
          rw [Equiv.Perm.mul_apply, hσ, Equiv.swap_apply_right]
        · intro σ₁ _ σ₂ _ h
          exact mul_left_cancel h
        · intro τ hτ
          refine ⟨Equiv.swap a b * τ, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
            rw [Equiv.Perm.mul_apply, hτ, Equiv.swap_apply_left]
          · rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
      have htot : Fintype.card (Equiv.Perm α)
          = ∑ b, (Finset.univ.filter (fun σ : Equiv.Perm α => σ i = b)).card := by
        rw [← Finset.card_univ]
        exact Finset.card_eq_sum_card_fiberwise (fun σ _ => Finset.mem_univ (σ i))
      simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at htot
      have hn : (Fintype.card α : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
      rw [htot]
      push_cast
      field_simp
    have hP : (Fintype.card (Equiv.Perm α) : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
    have hn : (Fintype.card α : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
    have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Equiv.Perm α)))
      (fun σ : Equiv.Perm α => σ i = a)
    have hsplitQ : ((Finset.univ.filter (fun σ : Equiv.Perm α => σ i = a)).card : ℚ)
        + ((Finset.univ.filter (fun σ : Equiv.Perm α => ¬ σ i = a)).card : ℚ)
        = Fintype.card (Equiv.Perm α) := by
      rw [Finset.card_univ] at hsplit
      exact_mod_cast hsplit
    unfold E slotScore
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hc : ((Finset.univ.filter (fun σ : Equiv.Perm α => ¬ σ i = a)).card : ℚ)
        = Fintype.card (Equiv.Perm α) - (Fintype.card (Equiv.Perm α) : ℚ) / Fintype.card α := by
      rw [← hfib i a]
      linarith
    rw [hc, hfib i a]
    field_simp
    ring
  have hEsum : ∀ (f : α → Equiv.Perm α → ℚ),
      E (fun σ => ∑ i, f i σ) = ∑ i, E (f i) := by
    intro f
    unfold E
    rw [Finset.sum_comm, Finset.sum_div]
  have hn : (Fintype.card α : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  have hdeck : deckScore ((Fintype.card α : ℚ) - 1) (-1) g
      = fun σ => ∑ i, slotScore ((Fintype.card α : ℚ) - 1) (-1) i (g i) σ := rfl
  rw [hdeck, hEsum]
  simp only [hslot]
  have h0 : ((Fintype.card α : ℚ) - 1 - -1) / (Fintype.card α : ℚ) + -1 = 0 := by
    field_simp
    ring
  simp [h0]
