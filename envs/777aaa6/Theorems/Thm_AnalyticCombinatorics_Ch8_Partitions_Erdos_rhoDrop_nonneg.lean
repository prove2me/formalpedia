-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_rhoDrop_nonneg
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.rhoDrop_nonneg
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:18:43.311319+00:00
-- url     : https://prove2.me/theorems/15068952-74a2-4dd4-bc6b-667509e8525e
-- title:
--   Supporting lemma: rhoDrop nonneg
-- statement:
--   Supporting lemma from AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma rhoDrop_nonneg {n m : ℕ} (_hm : m ≤ n) :
--       0 ≤ rhoDrop n m
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean#L169. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuTilde
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Assembly of the two-term expansion for `muNum`

This file only assembles the banked estimates:

* the infinite model two-term expansion,
* the two main-range errors,
* the weighted Erdős far tail,
* and a local model-product tail.
-/

open Filter Finset
open scoped Topology BigOperators

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.rhoDrop_nonneg {n m : ℕ} (_hm : m ≤ n) :
    0 ≤ rhoDrop n m := by sorry
