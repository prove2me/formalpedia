-- Prove2me | solution 1 for GCDMoment.all_prime_of_cardFactors_le_length
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T22:39:43.025092+00:00
-- url     : https://prove2.me/submissions/1539f0b0-5a92-46e8-a4a5-3ea82555b8f8

import Definitions.Def_Novelty_GCDMomentMultiplicative
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentRefinementOrder
import Definitions.Def_Novelty_GCDMomentTraceWitness
open GCDMoment ArithmeticFunction in
theorem solution :
    ∀ (l : List ℕ), (∀ a ∈ l, 2 ≤ a) → cardFactors l.prod ≤ l.length → ∀ a ∈ l, a.Prime := by
  have hge : ∀ (l : List ℕ), (∀ a ∈ l, 2 ≤ a) → l.length ≤ cardFactors l.prod := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a t ih =>
      intro h
      have ha : 2 ≤ a := h a List.mem_cons_self
      have ht : ∀ b ∈ t, 2 ≤ b := fun b hb => h b (List.mem_cons_of_mem _ hb)
      have hprod0 : t.prod ≠ 0 := by
        intro h0
        rw [List.prod_eq_zero_iff] at h0
        have := ht 0 h0
        omega
      rw [List.prod_cons, cardFactors_mul (by omega) hprod0, List.length_cons]
      have h1 : 0 < cardFactors a := cardFactors_pos_iff_one_lt.mpr (by omega)
      have := ih ht
      omega
  intro l
  induction l with
  | nil => intro _ _ a ha; simp at ha
  | cons a t ih =>
    intro h hle b hb
    have ha : 2 ≤ a := h a List.mem_cons_self
    have ht : ∀ c ∈ t, 2 ≤ c := fun c hc => h c (List.mem_cons_of_mem _ hc)
    have hprod0 : t.prod ≠ 0 := by
      intro h0
      rw [List.prod_eq_zero_iff] at h0
      have := ht 0 h0
      omega
    rw [List.prod_cons, cardFactors_mul (by omega) hprod0, List.length_cons] at hle
    have h1 : 0 < cardFactors a := cardFactors_pos_iff_one_lt.mpr (by omega)
    have h2 := hge t ht
    have hat : cardFactors a = 1 := by omega
    have htt : cardFactors t.prod ≤ t.length := by omega
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact cardFactors_eq_one_iff_prime.mp hat
    · exact ih ht htt b hb'
