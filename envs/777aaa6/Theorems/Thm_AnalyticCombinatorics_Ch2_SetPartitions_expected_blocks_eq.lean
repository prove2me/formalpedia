-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch2_SetPartitions_expected_blocks_eq
-- name    : AnalyticCombinatorics.Ch2.SetPartitions.expected_blocks_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T11:15:53.126981+00:00
-- url     : https://prove2.me/theorems/c10c75c3-cec6-45e9-96be-351acef03b37
-- title:
--   Mean block count for genuine finite set partitions
-- statement:
--   Let $\mathcal P_n$ be the finite set of set partitions of $\{0,\ldots,n-1\}$, let $b(P)$ be the number of blocks, and define $B_n=|\mathcal P_n|$. These are the source cardinality-defined Bell numbers. For every $n\in\mathbb N$ with $B_n>0$,
--
--   $$\frac{\sum_{P\in\mathcal P_n}b(P)}{B_n}=\frac{B_{n+1}}{B_n}-1.$$
--
--   The averages are rational. The positivity premise is retained, and no identification with the separately defined Bell EGF class is assumed.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/SetPartitions/BellMean.lean#L655. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_SetPartitions_BellMean
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Bell numbers as finite set partitions

This file uses `Finpartition (Finset.univ : Finset (Fin n))` as the type of genuine
set partitions of `[n]`.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch2 AnalyticCombinatorics.Ch2.SetPartitions

open Finset Function

-- The equivalences below transport `Finpartition`s through finset/subtype complements;
-- the larger heartbeat budget is for those local `simp`/`grind` calls.
set_option maxHeartbeats 400000

theorem AnalyticCombinatorics.Ch2.SetPartitions.expected_blocks_eq (n : ℕ) (hB : 0 < bellNumber n) :
    (∑ P : Finpartition (Finset.univ : Finset (Fin n)), (P.parts.card : ℚ)) / bellNumber n
      = bellNumber (n + 1) / bellNumber n - 1 := by sorry
