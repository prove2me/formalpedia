-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.odd_cofactor_of_dyadic_event
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:02:38.312806+00:00
-- url     : https://prove2.me/submissions/26d39961-8d2a-4c86-a07a-db686eef8be3

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DivisorCubeIncidence
import Mathlib

   
                                                 

                                                                 
                                                                          
                                                                           
                                                                     
  
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (r p n : ℕ) (hp : ¬ 2 ∣ p)
    (he : 2 ^ r * p ∣ n ∧ ¬ 2 * (2 ^ r * p) ∣ n) :
    ∃ u : ℕ, ¬ 2 ∣ u ∧ n = 2 ^ r * u := by
  obtain ⟨m, hm⟩ := he.1
  have hm2 : ¬ 2 ∣ m := by
    rintro ⟨v, hv⟩
    apply he.2
    refine ⟨v, ?_⟩
    rw [hm, hv]
    ring
  refine ⟨p * m, ?_, ?_⟩
  · intro h
    rcases Nat.prime_two.dvd_mul.mp h with h | h
    · exact hp h
    · exact hm2 h
  · simpa only [mul_assoc] using hm
end
