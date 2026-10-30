-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_main_model_rho_error_le
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.main_model_rho_error_le
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:23:06.396911+00:00
-- url     : https://prove2.me/theorems/22824ee2-d069-45d4-a77b-4bf952406219
-- title:
--   Second cross error
-- statement:
--   **Second cross error**: `∑_{1≤m≤⌊n^{2/3}⌋} |modelSummand|·|rhoDrop − rhoDropModel| ≤ K/n`.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem main_model_rho_error_le :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
--         (∑ m ∈ Finset.Icc 1 ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊,
--           |modelSummand n m| * |rhoDrop n m - rhoDropModel n m|)
--         ≤ K / (n:ℝ)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuNumModelRhoError.lean#L153. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuNumModel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuTilde
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Second cross error for the `muNum` two-term expansion

`∑_{1≤m≤⌊n^{2/3}⌋} |modelSummand n m| · |rhoDrop n m − rhoDropModel n m| ≤ K/n`.

The `modelSummand·(rhoDrop − rhoDropModel)` cross term: the `modelSummand` magnitude
(`|modelSummand| ≤ (1/n)g₀ + (1/n²)g₁ + (C/(8n²√n))g₂`) times the second-order `ρ`-drop error
(`|rhoDrop − rhoDropModel| ≤ 3m³/(√n)⁵`, `rhoDrop_sub_model_le`), expanded into the three shifted
Lambert moments `M₃,M₄,M₅` and bounded by `sigmaMoment_le_power_sharp`.  Sibling of
`main_kernel_error_rhoModel_le`, one fewer kernel factor.  Opus-authored.
-/

set_option maxHeartbeats 4000000

open Filter Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.main_model_rho_error_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (∑ m ∈ Finset.Icc 1 ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊,
        |modelSummand n m| * |rhoDrop n m - rhoDropModel n m|)
      ≤ K / (n:ℝ) := by sorry
