-- Prove2me | solution 1 for RainbowAP.sum_missCount_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:20:23.569166+00:00
-- url     : https://prove2.me/submissions/e2ba2ee1-cf82-4f32-a41c-e5f6ddf781a4

-- Sol generated from Shared/RainbowAPSpectrumMoments.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumMoments
import Theorems.Thm_RainbowAP_card_avoid_two

open Finset

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]





/-- Words over `α` of length `m` avoiding one fixed letter. -/
lemma card_avoid_one (m : ℕ) (a : α) :
    (univ.filter (fun f : Fin m → α => ∀ x, f x ≠ a)).card
      = (Fintype.card α - 1) ^ m := by
  have h : (univ.filter (fun f : Fin m → α => ∀ x, f x ≠ a))
      = Fintype.piFinset (fun _ : Fin m => univ.erase a) := by
    ext f
    simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset]
  simp [Finset.card_erase_of_mem]


lemma missCount_eq_sum {m : ℕ} (f : Fin m → α) :
    missCount f = ∑ a : α, (if (∀ x, f x ≠ a) then 1 else 0) := by
  rw [missCount, missing, Finset.card_filter]




open RainbowAP in
lemma solution(m : ℕ) :
    ∑ f : Fin m → α, (missCount f) ^ 2
      = Fintype.card α * (Fintype.card α - 1) ^ m
        + Fintype.card α * (Fintype.card α - 1) * (Fintype.card α - 2) ^ m := by
  have key : ∀ f : Fin m → α, (missCount f) ^ 2
      = ∑ a : α, ∑ b : α, (if ((∀ x, f x ≠ a) ∧ (∀ x, f x ≠ b)) then 1 else 0) := by
    intro f
    rw [sq, missCount_eq_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    by_cases ha : (∀ x, f x ≠ a) <;> by_cases hb : (∀ x, f x ≠ b) <;> simp [ha, hb]
  simp_rw [key]
  have swap : (∑ f : Fin m → α, ∑ a : α, ∑ b : α,
        (if ((∀ x, f x ≠ a) ∧ (∀ x, f x ≠ b)) then 1 else 0))
      = ∑ a : α, ∑ b : α, ∑ f : Fin m → α,
        (if ((∀ x, f x ≠ a) ∧ (∀ x, f x ≠ b)) then 1 else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
  rw [swap]
  have step : ∀ a : α, (∑ b : α, ∑ f : Fin m → α,
      (if ((∀ x, f x ≠ a) ∧ (∀ x, f x ≠ b)) then 1 else 0))
      = (Fintype.card α - 1) ^ m + (Fintype.card α - 1) * (Fintype.card α - 2) ^ m := by
    intro a
    have hdiag : (∑ f : Fin m → α, (if ((∀ x, f x ≠ a) ∧ (∀ x, f x ≠ a)) then 1 else 0))
        = (Fintype.card α - 1) ^ m := by
      rw [← Finset.card_filter, ← card_avoid_one m a]
      congr 1
      ext f
      simp [and_self]
    have hoff : ∀ b : α, b ≠ a → (∑ f : Fin m → α,
        (if ((∀ x, f x ≠ a) ∧ (∀ x, f x ≠ b)) then 1 else 0))
        = (Fintype.card α - 2) ^ m := by
      intro b hb
      rw [← Finset.card_filter, card_avoid_two m a b (Ne.symm hb)]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a), hdiag]
    rw [Finset.sum_congr rfl (fun b hb => hoff b (Finset.mem_erase.1 hb).1)]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a)]
    simp [Finset.card_univ, add_comm]
  rw [Finset.sum_congr rfl (fun a _ => step a)]
  simp [Finset.card_univ, mul_add, mul_assoc]
