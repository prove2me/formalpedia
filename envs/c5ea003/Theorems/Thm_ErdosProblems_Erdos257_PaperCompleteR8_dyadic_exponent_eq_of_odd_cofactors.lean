-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_dyadic_exponent_eq_of_odd_cofactors
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.dyadic_exponent_eq_of_odd_cofactors
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:24:31.084182+00:00
-- url     : https://prove2.me/theorems/03976aa6-9578-4881-ae9d-7d9987c0a77b
-- title:
--   Odd cofactors determine the dyadic exponent
-- statement:
--   If 2^k d=2^l e and both cofactors d,e are odd, then k=l.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/DyadicDivisorFrames.lean#L14-L30
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
import Mathlib

/-! # Disjoint dyadic divisor frames for the weighted separating host

These are the actual frames F_k = {2^(k+2) d : d divides M_k}. Positive odd
M_k make them pairwise disjoint and give an infinite positive union. The
prime-block harmonic bounds, weighted summability and divergent logarithmic
means are further obligations, not hypotheses hidden in a class-separation
conclusion.
-/
open Finset

open ErdosProblems.Erdos257.PaperCompleteR8

theorem ErdosProblems.Erdos257.PaperCompleteR8.dyadic_exponent_eq_of_odd_cofactors {k l d e : ℕ}
    (hd : ¬ 2 ∣ d) (he : ¬ 2 ∣ e)
    (h : 2 ^ k * d = 2 ^ l * e) : k = l := by sorry
