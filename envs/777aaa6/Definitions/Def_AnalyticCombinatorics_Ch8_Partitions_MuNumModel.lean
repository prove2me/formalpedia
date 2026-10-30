-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuNumModel
-- name    : AnalyticCombinatorics_Ch8_Partitions_MuNumModel
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:19:45.946741+00:00
-- url     : https://prove2.me/theorems/84ecc10b-0827-4996-a2f0-b74d354f06c7
-- title:
--   Mu Num Model
-- statement:
--   The imported mathematical setting is specified by the exact source-linked module below. Compiler facts must determine whether this module contributes nonproof material; no empty-owner claim or separate mathematical definition is inferred from this source inventory.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuNumModel.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Numerator model: the second-order `ρ`-drop and its error

The drift numerator is `muNum n = ∑_m erdosWeight n m · rhoDrop n m` with
`rhoDrop n m = 3(√n − √(n−m))`.  Its model replaces the `√`-drop by its two-term Taylor
expansion (`sqrt_drop_second_order`):

  `rhoDropModel n m = 3( m/(2√n) + m²/(8(√n)³) )`,   `|rhoDrop − rhoDropModel| ≤ 3 m³/(√n)⁵`.

This is the `ρ`-drop half of the `muNum` expansion (the kernel half is the banked `modelSummand`).
Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The two-term Taylor model of the smooth-rank drop `3(√n − √(n−m))`. -/
noncomputable def rhoDropModel (n m : ℕ) : ℝ :=
  3 * ((m : ℝ) / (2 * Real.sqrt (n : ℝ)) + (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3))

end AnalyticCombinatorics.Ch8.Partitions.Erdos


