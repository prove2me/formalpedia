-- Prove2me | solution 1 for RainbowAP.card_avoid_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:19:10.270103+00:00
-- url     : https://prove2.me/submissions/f14d0fe2-f0ad-474e-91e5-1cdf4c43b70e

-- Sol generated from Shared/RainbowAPSpectrumMoments.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumMoments

open Finset

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]











open RainbowAP in
lemma solution(m : ℕ) (a b : α) (hab : a ≠ b) :
    (univ.filter (fun f : Fin m → α => (∀ x, f x ≠ a) ∧ (∀ x, f x ≠ b))).card
      = (Fintype.card α - 2) ^ m := by
  have h1 : (univ.filter (fun f : Fin m → α => (∀ x, f x ≠ a) ∧ (∀ x, f x ≠ b)))
      = Fintype.piFinset (fun _ : Fin m => (univ.erase a).erase b) := by
    ext f
    simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, forall_and]
    tauto
  have h2 : ((univ.erase a).erase b).card = Fintype.card α - 2 := by
    rw [Finset.card_erase_of_mem (by simp [hab.symm]), Finset.card_erase_of_mem (by simp)]
    simp [Finset.card_univ]
    omega
  rw [h1, Fintype.card_piFinset]
  simp [h2]
