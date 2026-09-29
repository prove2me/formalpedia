-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.log_nat_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:02:35.108223+00:00
-- url     : https://prove2.me/submissions/6edefb2f-5bed-48d9-b913-da763981ada8

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
theorem solution (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
end
