-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.dyadicBlockCount_cast
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:02:29.527567+00:00
-- url     : https://prove2.me/submissions/30a321eb-0272-457b-ab66-b45ab4c82d9a

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
theorem solution (P : Finset ℕ) (r n : ℕ) :
    (dyadicBlockCount P r n : ℝ) =
      ∑ p ∈ P, if 2 ^ r * p ∣ n ∧ ¬ 2 * (2 ^ r * p) ∣ n then (1 : ℝ) else 0 := by
  classical
  symm
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one, dyadicBlockCount]
end
