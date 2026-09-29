-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_odd_cofactor_of_dyadic_event
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.odd_cofactor_of_dyadic_event
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:25:37.259988+00:00
-- url     : https://prove2.me/theorems/aa5761ce-05e7-40cd-8fe7-6fd588708996
-- title:
--   A dyadic event has an odd cofactor
-- statement:
--   If p is odd and n is divisible by 2^r p but not by 2^(r+1) p, then n is 2^r times an odd natural number.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/DivisorCubeIncidence.lean#L118-L134
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DivisorCubeIncidence
import Mathlib

   
                                                 

                                                                 
                                                                          
                                                                           
                                                                     
  
noncomputable section
open Finset

open ErdosProblems.Erdos257.PaperCompleteR8

theorem ErdosProblems.Erdos257.PaperCompleteR8.odd_cofactor_of_dyadic_event (r p n : ℕ) (hp : ¬ 2 ∣ p)
    (he : 2 ^ r * p ∣ n ∧ ¬ 2 * (2 ^ r * p) ∣ n) :
    ∃ u : ℕ, ¬ 2 ∣ u ∧ n = 2 ^ r * u := by sorry
end
