-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdosWeight_nonneg_of_lt
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.erdosWeight_nonneg_of_lt
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:17:23.735516+00:00
-- url     : https://prove2.me/theorems/a128cb12-650a-4d60-99b2-b1a545d90e43
-- title:
--   Supporting lemma: erdosWeight nonneg of lt
-- statement:
--   Supporting lemma from AnalyticCombinatorics/Ch8/Partitions/ErdosKernel.lean.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma erdosWeight_nonneg_of_lt {n m : ℕ} (hmn : m < n) :
--       0 ≤ erdosWeight n m
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/ErdosKernel.lean#L124. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

open Filter
open scoped BigOperators Topology

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.erdosWeight_nonneg_of_lt {n m : ℕ} (hmn : m < n) :
    0 ≤ erdosWeight n m := by sorry
