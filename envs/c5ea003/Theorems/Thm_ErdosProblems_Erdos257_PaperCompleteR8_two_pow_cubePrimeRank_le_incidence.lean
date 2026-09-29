-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_two_pow_cubePrimeRank_le_incidence
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.two_pow_cubePrimeRank_le_incidence
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:25:24.512822+00:00
-- url     : https://prove2.me/theorems/4aa28d4e-c726-4d2e-9194-0b12223e3045
-- title:
--   Divisor-cube incidence dominates an exponential prime rank
-- statement:
--   For positive q,n with q dividing n, and a finite prime set P, the number of divisor-cube elements dividing n is at least 2 raised to cubePrimeRank q P n.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/DivisorCubeIncidence.lean#L45-L87
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DivisorCubeIncidence
import Mathlib

   
                                                 

                                                                 
                                                                          
                                                                           
                                                                     
  
noncomputable section
open Finset

open ErdosProblems.Erdos257.PaperCompleteR8

theorem ErdosProblems.Erdos257.PaperCompleteR8.two_pow_cubePrimeRank_le_incidence (q : ℕ) (P : Finset ℕ) (n : ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) (hn : 0 < n) (hqn : q ∣ n) :
    2 ^ cubePrimeRank q P n ≤ ((divisorCube q P).filter (fun a => a ∣ n)).card := by sorry
end
