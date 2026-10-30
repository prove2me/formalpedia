-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_Pker_highclump
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.Pker_highclump
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:31:39.390992+00:00
-- url     : https://prove2.me/theorems/9f9c3fb0-f095-4fff-bb51-f5b130f4a92c
-- title:
--   Conditional separated positive kernel clumps
-- statement:
--   Separated positive one-step jump clumps with explicit kernel-mass and size premises; final full conditioned-walk variance/occupation hypotheses are not discharged here.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma Pker_highclump {x : ℕ} (hx : 100 ≤ x) (hkmx : kernelMass x ≤ 2) (hkmx0 : 0 < kernelMass x) :
--       (Real.exp (-C * 2) / 13
--           ≤ ∑ a ∈ Finset.Icc (x - 2 * Nat.sqrt x) (x - 7 * Nat.sqrt x / 4), Pker x a)
--         ∧ (∀ a ∈ Finset.Icc (x - 2 * Nat.sqrt x) (x - 7 * Nat.sqrt x / 4),
--             (21 : ℝ) / 10 ≤ 3 * (Real.sqrt (x : ℝ) - Real.sqrt (a : ℝ)))
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/VarianceConcrete.lean#L219. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Concrete `v0`: single-chain jump-window mass for the Erdős kernel (renewal route B)

Builds toward the positive local-variance input `v0 > 0`.  `Pker_subwindow_mass` lower-bounds the
single-chain `Pker x ·` mass on a jump sub-window `[a, b] ⊆ [⌊√x⌋, 2⌊√x⌋]` via the banked per-term
`Pker_lower`.  Splitting the window into a LOW and a HIGH jump sub-window gives two separated
ρ-decrement clumps, which `product_locVar_ge` (VarianceLower) turns into `v0 > 0`.
-/

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.Pker_highclump {x : ℕ} (hx : 100 ≤ x) (hkmx : kernelMass x ≤ 2) (hkmx0 : 0 < kernelMass x) :
    (Real.exp (-C * 2) / 13
        ≤ ∑ a ∈ Finset.Icc (x - 2 * Nat.sqrt x) (x - 7 * Nat.sqrt x / 4), Pker x a)
      ∧ (∀ a ∈ Finset.Icc (x - 2 * Nat.sqrt x) (x - 7 * Nat.sqrt x / 4),
          (21 : ℝ) / 10 ≤ 3 * (Real.sqrt (x : ℝ) - Real.sqrt (a : ℝ))) := by sorry
