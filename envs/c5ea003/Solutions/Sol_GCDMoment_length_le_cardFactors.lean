-- Prove2me | solution 1 for GCDMoment.length_le_cardFactors
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T22:34:53.767644+00:00
-- url     : https://prove2.me/submissions/1165ef2b-2013-452f-a3bb-907ca350bd51

import Definitions.Def_Novelty_GCDMomentMultiplicative
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentRefinementOrder
import Definitions.Def_Novelty_GCDMomentTraceWitness
open GCDMoment ArithmeticFunction in
theorem solution :
    ∀ (l : List ℕ), (∀ a ∈ l, 2 ≤ a) → l.length ≤ cardFactors l.prod := by
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
