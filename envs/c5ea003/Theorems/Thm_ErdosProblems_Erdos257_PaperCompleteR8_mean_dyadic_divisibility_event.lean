-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_mean_dyadic_divisibility_event
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.mean_dyadic_divisibility_event
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:25:39.948863+00:00
-- url     : https://prove2.me/theorems/2dc7d9fc-d1f5-40f3-82bb-ec26422b8469
-- title:
--   Exact mean of a dyadic divisibility event
-- statement:
--   If d>0, X>0, and 2d divides X, then the proportion of n from 1 through X divisible by d but not 2d is exactly 1/(2d).
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/DyadicLogarithmicEvents.lean#L47-L60
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

theorem ErdosProblems.Erdos257.PaperCompleteR8.mean_dyadic_divisibility_event (d X : ℕ) (hd : 0 < d)
    (hX : 0 < X) (hperiod : 2 * d ∣ X) :
    (∑ n ∈ Icc 1 X, if d ∣ n ∧ ¬ 2 * d ∣ n then (1 : ℝ) else 0) /
        (X : ℝ) = 1 / (2 * (d : ℝ)) := by sorry
