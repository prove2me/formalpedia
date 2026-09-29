-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_dyadic_union_log_pointwise
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.dyadic_union_log_pointwise
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:25:50.742117+00:00
-- url     : https://prove2.me/theorems/4acc43d1-2834-4079-8417-31ae63ebe8c1
-- title:
--   Dyadic events bound the logarithm of frame divisor counts
-- statement:
--   For finite odd-prime blocks P_k and a finite set of block indices J, the number of active dyadic divisibility events at a positive n, multiplied by log 2, is at most the logarithm of the number of divisors of n in the union of the corresponding dyadic frames.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/DivisorCubeIncidence.lean#L145-L200
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DivisorCubeIncidence
import Mathlib

   
                                                 

                                                                 
                                                                          
                                                                           
                                                                     
  
noncomputable section
open Finset

open ErdosProblems.Erdos257.PaperCompleteR8

theorem ErdosProblems.Erdos257.PaperCompleteR8.dyadic_union_log_pointwise (P : ℕ → Finset ℕ) (J : Finset ℕ) (n : ℕ)
    (hn : 0 < n) (hP : ∀ k p, p ∈ P k → Nat.Prime p ∧ 2 < p) :
    Real.log 2 * (∑ k ∈ J, (dyadicBlockCount (P k) (k + 2) n : ℝ)) ≤
      Real.log (((J.biUnion (fun k => dyadicDivisorFrame ((P k).prod id) k)).filter
        (fun a => a ∣ n)).card : ℝ) := by sorry
end
