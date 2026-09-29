-- Prove2me | Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
-- name    : ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:44:11.198617+00:00
-- url     : https://prove2.me/theorems/ca1f8a9c-8640-465b-99b7-4de9f50e4c96
-- title:
--   Dyadic divisor frames and their host
-- statement:
--   Defines a finite frame formed from divisors of an integer at a dyadic scale, and the support obtained from a sequence of such frames.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/DyadicDivisorFrames.lean#L1-L73
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Mathlib

/-! # Disjoint dyadic divisor frames for the weighted separating host

These are the actual frames F_k = {2^(k+2) d : d divides M_k}. Positive odd
M_k make them pairwise disjoint and give an infinite positive union. The
prime-block harmonic bounds, weighted summability and divergent logarithmic
means are further obligations, not hypotheses hidden in a class-separation
conclusion.
-/
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset



def dyadicDivisorFrame (M k : ℕ) : Finset ℕ :=
  M.divisors.image (fun d => 2 ^ (k + 2) * d)

def dyadicDivisorHost (M : ℕ → ℕ) : Set ℕ :=
  {a | ∃ k, a ∈ dyadicDivisorFrame (M k) k}







end ErdosProblems.Erdos257.PaperCompleteR8


