-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_card_dyadic_divisibility_event
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.card_dyadic_divisibility_event
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:07:27.522168+00:00
-- url     : https://prove2.me/theorems/8cdf3434-7c17-47de-96aa-e83d99e0b89c
-- title:
--   Count exact dyadic divisibility events
-- statement:
--   For positive d and any X, the number of integers n from 1 through X divisible by d but not by 2d is ⌊X/d⌋−⌊X/(2d)⌋.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/DyadicLogarithmicEvents.lean#L13-L29
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

theorem ErdosProblems.Erdos257.PaperCompleteR8.card_dyadic_divisibility_event (d X : ℕ) (hd : 0 < d) :
    ((Icc 1 X).filter (fun n => d ∣ n ∧ ¬ 2 * d ∣ n)).card =
      X / d - X / (2 * d) := by sorry
