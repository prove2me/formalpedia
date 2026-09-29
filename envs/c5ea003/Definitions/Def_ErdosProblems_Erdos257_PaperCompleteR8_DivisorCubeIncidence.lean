-- Prove2me | Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DivisorCubeIncidence
-- name    : ErdosProblems_Erdos257_PaperCompleteR8_DivisorCubeIncidence
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:53:53.896989+00:00
-- url     : https://prove2.me/theorems/90ddb9f6-7eef-4305-82e8-18d3a7fe7782
-- title:
--   Divisor cubes and prime-incidence counts
-- statement:
--   This bundle defines a divisor cube q times the divisors of the prime-set product, counts primes p in P for which qp divides n, and counts primes p at a specified exact dyadic divisibility level.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/DivisorCubeIncidence.lean#L1-L203
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
import Mathlib

   
                                                 

                                                                 
                                                                          
                                                                           
                                                                     
  
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset

/-- The literal finite divisor cube used in the paper. -/
def divisorCube (q : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (P.prod id).divisors.image (fun d => q * d)

/-- Primes which can be inserted after the mandatory factor q. -/
def cubePrimeRank (q : ℕ) (P : Finset ℕ) (n : ℕ) : ℕ :=
  (P.filter (fun p => q * p ∣ n)).card









/-- Exact dyadic row events, counted as a finite cardinality. -/
def dyadicBlockCount (P : Finset ℕ) (r n : ℕ) : ℕ :=
  (P.filter (fun p => 2 ^ r * p ∣ n ∧ ¬ 2 * (2 ^ r * p) ∣ n)).card









end ErdosProblems.Erdos257.PaperCompleteR8
end


