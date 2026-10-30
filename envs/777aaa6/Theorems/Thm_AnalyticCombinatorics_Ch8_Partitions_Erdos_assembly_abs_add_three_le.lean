-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_assembly_abs_add_three_le
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.assembly_abs_add_three_le
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:17:15.86643+00:00
-- url     : https://prove2.me/theorems/89650dcd-5979-4e2a-80fd-f8f8dba959f0
-- title:
--   Supporting lemma: assembly abs add three le
-- statement:
--   Supporting lemma from AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma assembly_abs_add_three_le (a b c : ℝ) :
--       |a + b + c| ≤ |a| + |b| + |c|
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean#L25. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.assembly_abs_add_three_le (a b c : ℝ) :
    |a + b + c| ≤ |a| + |b| + |c| := by sorry
