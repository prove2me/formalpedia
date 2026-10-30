-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_muNum_split_main_tail
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.muNum_split_main_tail
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:18:01.272266+00:00
-- url     : https://prove2.me/theorems/3d52e79d-3e1d-46a0-81ac-f09da343cbeb
-- title:
--   Supporting lemma: muNum split main tail
-- statement:
--   Supporting lemma from AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma muNum_split_main_tail (n M : ℕ) (hMle : M ≤ n - 1) :
--       muNum n =
--         (∑ m ∈ Finset.Icc 1 M, erdosWeight n m * rhoDrop n m)
--         + (∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m * rhoDrop n m)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean#L883. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.muNum_split_main_tail (n M : ℕ) (hMle : M ≤ n - 1) :
    muNum n =
      (∑ m ∈ Finset.Icc 1 M, erdosWeight n m * rhoDrop n m)
      + (∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m * rhoDrop n m) := by sorry
