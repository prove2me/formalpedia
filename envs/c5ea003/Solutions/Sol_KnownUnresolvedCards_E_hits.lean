-- Prove2me | solution 1 for KnownUnresolvedCards.E_hits
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T07:18:16.162643+00:00
-- url     : https://prove2.me/submissions/6b0a9e47-78de-46a5-bda4-45654613d348

import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
import Definitions.Def_MachineLearning_KnownUnresolvedCards_DeckGame
import Definitions.Def_MachineLearning_KnownUnresolvedCards_PermCount

open KnownUnresolvedCards Finset

open KnownUnresolvedCards Finset in
/-- **A uniformly random permutation agrees with any fixed map in one position on average.** -/
theorem solution {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] (g : α → α) :
    E (fun σ : Equiv.Perm α => (hits g σ : ℚ)) = 1 := by
  classical
  have hnpos : 0 < Fintype.card α := Fintype.card_pos
  have hfib : ∀ (i j : α), (Finset.univ.filter (fun σ : Equiv.Perm α => σ i = j)).card
      = (Finset.univ.filter (fun σ : Equiv.Perm α => σ i = g i)).card := by
    intro i j
    refine Finset.card_nbij' (fun σ => Equiv.swap j (g i) * σ) (fun σ => Equiv.swap j (g i) * σ)
      ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
      rw [Equiv.Perm.mul_apply, hσ, Equiv.swap_apply_left]
    · intro σ hσ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
      rw [Equiv.Perm.mul_apply, hσ, Equiv.swap_apply_right]
    · intro σ _; exact Equiv.swap_mul_self_mul _ _ _
    · intro σ _; exact Equiv.swap_mul_self_mul _ _ _
  have hc : ∀ i : α, (Finset.univ.filter (fun σ : Equiv.Perm α => σ i = g i)).card
      * Fintype.card α = (Fintype.card α).factorial := by
    intro i
    have h := Finset.card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm α => σ i)
      (s := Finset.univ) (t := Finset.univ) (fun σ _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_perm] at h
    rw [h, Finset.sum_congr rfl (fun j _ => hfib i j), Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_comm]
  have hsum : ∑ σ : Equiv.Perm α, hits g σ = (Fintype.card α).factorial := by
    have e1 : ∑ σ : Equiv.Perm α, hits g σ
        = ∑ i : α, (Finset.univ.filter (fun σ : Equiv.Perm α => σ i = g i)).card := by
      simp only [hits, Finset.card_filter]
      exact Finset.sum_comm
    rw [e1]
    apply Nat.eq_of_mul_eq_mul_right hnpos
    rw [Finset.sum_mul, Finset.sum_congr rfl (fun i _ => hc i), Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_comm]
  unfold E
  rw [← Nat.cast_sum, hsum, Fintype.card_perm]
  exact div_self (by exact_mod_cast Nat.factorial_ne_zero _)
