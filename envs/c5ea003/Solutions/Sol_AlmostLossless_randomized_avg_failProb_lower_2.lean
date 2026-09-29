-- Prove2me | solution 2 for AlmostLossless.randomized_avg_failProb_lower
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T12:30:23.029545+00:00
-- url     : https://prove2.me/submissions/efa5ee6d-b716-4d8f-a5e5-1c3317144286

import Definitions.Def_Logic_AlmostLossless_Core
open AlmostLossless in
theorem solution {S : Type*} {C : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype C]
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (K : Ω → Code S C) :
    1 - (Fintype.card C : ℚ) / (Fintype.card S : ℚ)
      ≤ avgFailProb uniformSource K := by
  have hcorr : ∀ K : Code S C, (({s | Correct K s} : Finset S).card) ≤ Fintype.card C := by
    intro K
    have hinj : Set.InjOn K.enc ({s | Correct K s} : Finset S) := by
      intro x hx y hy hxy
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Correct] at hx hy
      have : some x = some y := by rw [← hx, ← hy, hxy]
      exact Option.some.inj this
    have := Finset.card_le_card_of_injOn K.enc (fun x _ => Finset.mem_univ (K.enc x)) hinj
    simpa using this
  have hfail : ∀ K : Code S C,
      1 - (Fintype.card C : ℚ) / (Fintype.card S : ℚ) ≤ failProb uniformSource K := by
    intro K
    have hSpos : (0 : ℚ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset S)) (fun s => Correct K s)
    have hc : ((({s | Correct K s} : Finset S).card : ℕ) : ℚ) ≤ Fintype.card C := by
      exact_mod_cast hcorr K
    have hfp : failProb uniformSource K
        = ((({s | ¬ Correct K s} : Finset S).card : ℕ) : ℚ) / (Fintype.card S : ℚ) := by
      unfold failProb uniformSource
      rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    rw [Finset.card_univ] at hsplit
    have hsplitQ : ((({s | Correct K s} : Finset S).card : ℕ) : ℚ)
        + ((({s | ¬ Correct K s} : Finset S).card : ℕ) : ℚ) = Fintype.card S := by
      exact_mod_cast hsplit
    rw [hfp, le_div_iff₀ hSpos]
    have hexp : (1 - (Fintype.card C : ℚ) / (Fintype.card S : ℚ)) * (Fintype.card S : ℚ)
        = (Fintype.card S : ℚ) - Fintype.card C := by
      field_simp
    rw [hexp]
    linarith
  unfold avgFailProb
  have hΩ : (0 : ℚ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  rw [le_div_iff₀ hΩ]
  calc (1 - (Fintype.card C : ℚ) / (Fintype.card S : ℚ)) * (Fintype.card Ω : ℚ)
      = ∑ _ω : Ω, (1 - (Fintype.card C : ℚ) / (Fintype.card S : ℚ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ ω, failProb uniformSource (K ω) := Finset.sum_le_sum (fun ω _ => hfail (K ω))
