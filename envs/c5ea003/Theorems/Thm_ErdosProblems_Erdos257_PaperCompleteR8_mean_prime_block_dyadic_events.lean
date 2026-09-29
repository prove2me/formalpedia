-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_mean_prime_block_dyadic_events
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.mean_prime_block_dyadic_events
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:25:55.139835+00:00
-- url     : https://prove2.me/theorems/c2b316e9-be10-41a2-aa31-6e7b685d3cab
-- title:
--   Exact mean of prime-block dyadic events
-- statement:
--   If P is a finite set of positive integers and X>0 is divisible by 2·2^r·p for every p∈P, then the average over 1,…,X of the number of p whose 2^r p divides n but 2^(r+1) p does not is (∑_{p∈P}1/p)/(2·2^r).
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/DyadicLogarithmicEvents.lean#L62-L79
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
import Mathlib

namespace ErdosProblems.Erdos257.PaperCompleteR8
end ErdosProblems.Erdos257.PaperCompleteR8

/-! # Exact finite-period counts for dyadic logarithmic events

For the separating divisor frames, the event for a prime in row k is
2^(k+2)*p divides n but 2^(k+3)*p does not. Counting it by subtraction
avoids probabilistic independence assumptions or limiting density suppliers.
-/
open Finset

open ErdosProblems.Erdos257.PaperCompleteR8

theorem ErdosProblems.Erdos257.PaperCompleteR8.mean_prime_block_dyadic_events (P : Finset ℕ) (r X : ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hX : 0 < X)
    (hperiod : ∀ p ∈ P, 2 * (2 ^ r * p) ∣ X) :
    (∑ n ∈ Icc 1 X, ∑ p ∈ P,
      if 2 ^ r * p ∣ n ∧ ¬ 2 * (2 ^ r * p) ∣ n then (1 : ℝ) else 0) /
        (X : ℝ) =
      (∑ p ∈ P, (1 : ℝ) / p) / (2 * (2 : ℝ) ^ r) := by sorry
