-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_main_kernel_error_rhoModel_le
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.main_kernel_error_rhoModel_le
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:22:22.298304+00:00
-- url     : https://prove2.me/theorems/b5862509-4ff4-453c-841c-1b6238034d9f
-- title:
--   Supporting lemma: main kernel error rhoModel le
-- statement:
--   Supporting lemma from AnalyticCombinatorics/Ch8/Partitions/MuNumMainError.lean.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem main_kernel_error_rhoModel_le :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
--         (∑ m ∈ Finset.Icc 1 ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊,
--           |erdosWeight n m - modelSummand n m| * |rhoDropModel n m|)
--         ≤ K / (n:ℝ)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuNumMainError.lean#L11. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuNumModel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Main-range cross error for the `muNum` two-term expansion

`∑_{1≤m≤⌊n^{2/3}⌋} |erdosWeight n m − modelSummand n m| · |rhoDropModel n m| ≤ K/n`.

The `(erdosWeight − modelSummand)·rhoDropModel` cross term of `muNum − muNumModel`: the kernel error
(`erdosWeight_sub_model_le`) times the two-term `ρ`-drop model, expanded into the six shifted Lambert
moments `M₃,M₄,M₄,M₅,M₅,M₆` and bounded by `sigmaMoment_le_power_sharp`.
ChatGPT-drafted (R-series), recovered from `/tmp/ans_four_main_lemmas.txt` and verified.
-/

open Filter Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
set_option maxHeartbeats 4000000

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.main_kernel_error_rhoModel_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (∑ m ∈ Finset.Icc 1 ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊,
        |erdosWeight n m - modelSummand n m| * |rhoDropModel n m|)
      ≤ K / (n:ℝ) := by sorry
