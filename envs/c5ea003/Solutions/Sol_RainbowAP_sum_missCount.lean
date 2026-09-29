-- Prove2me | solution 1 for RainbowAP.sum_missCount
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:19:09.726606+00:00
-- url     : https://prove2.me/submissions/8ceb0424-fac3-48bf-bbee-8c7407d18591

-- Sol generated from Shared/RainbowAPSpectrumMoments.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumMoments

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
    ∑ f : Fin m → α, missCount f = Fintype.card α * (Fintype.card α - 1) ^ m := by
  simp_rw [missCount_eq_sum]
  rw [Finset.sum_comm]
  have h : ∀ a : α, (∑ f : Fin m → α, (if (∀ x, f x ≠ a) then 1 else 0))
      = (Fintype.card α - 1) ^ m := by
    intro a
    rw [← Finset.card_filter, card_avoid_one]
  rw [Finset.sum_congr rfl (fun a _ => h a)]
  simp [Finset.card_univ]
