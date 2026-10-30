-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch2_SetPartitions_BellVariance_variance_blocks_eq
-- name    : AnalyticCombinatorics.Ch2.SetPartitions.BellVariance.variance_blocks_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T11:16:03.751121+00:00
-- url     : https://prove2.me/theorems/1eeb9d97-fbff-4cb4-ae24-6d4055d2756f
-- title:
--   Variance of block count for genuine finite set partitions
-- statement:
--   Let $\mathcal P_n$ be the finite set of set partitions of $\{0,\ldots,n-1\}$, let $b(P)$ be the number of blocks, and define $B_n=|\mathcal P_n|$. These are the source cardinality-defined Bell numbers. For $n\in\mathbb N$ with $B_n>0$, the rational variance under uniform counting on $\mathcal P_n$ is
--
--   $$\frac{\sum_{P\in\mathcal P_n}b(P)^2}{B_n}-\left(\frac{\sum_{P\in\mathcal P_n}b(P)}{B_n}\right)^2=\frac{B_{n+2}}{B_n}-2\frac{B_{n+1}}{B_n}-\left(\frac{B_{n+1}}{B_n}-1\right)^2.$$
--
--   The source cardinality definition and explicit positivity assumption are unchanged.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/SetPartitions/BellVariance.lean#L658. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_SetPartitions_BellMean
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Second moment and variance for Bell set partitions

This file refines the add-one-element fiber count from the first-moment Bell
identity to a weighted identity, then derives the second moment and variance.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch2 AnalyticCombinatorics.Ch2.SetPartitions

open Finset Function

-- The local `Finpartition.ofExistsUnique` fiber constructors create large goals.
set_option maxHeartbeats 400000

theorem AnalyticCombinatorics.Ch2.SetPartitions.BellVariance.variance_blocks_eq (n : ℕ) (hB : 0 < bellNumber n) :
    (∑ P : Finpartition (Finset.univ : Finset (Fin n)), (P.parts.card : ℚ)^2) / bellNumber n
      - ((∑ P : Finpartition (Finset.univ : Finset (Fin n)), (P.parts.card : ℚ))
          / bellNumber n)^2
      =
        bellNumber (n + 2) / bellNumber n
        - 2 * bellNumber (n + 1) / bellNumber n
        - (bellNumber (n + 1) / bellNumber n - 1)^2 := by sorry
