-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosAlignConnect
-- name    : AnalyticCombinatorics_Ch8_Partitions_ErdosAlignConnect
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:55:26.486509+00:00
-- url     : https://prove2.me/theorems/c7b65b08-b38d-403b-b4cc-46125f6eea7b
-- title:
--   Erdos Align Connect
-- statement:
--   The source mathematical objects and operations are specified by the following definitions.
--
--   ```lean
--   def ErdosAlignment (J : ℕ) : Prop :=
--     ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
--       ∀ (m : ℕ) (ε : ℝ), 0 < ε → ∃ R₀ : ℕ, ∀ i j, R₀ ≤ rnk i → R₀ ≤ rnk j →
--         1 - (1 - δ) ^ m - ε ≤ ∑ k ∈ Finset.range (max i j + 1),
--             min (KPowK m (killedKer Pker rnk J) i k) (KPowK m (killedKer Pker rnk J) j k)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/ErdosAlignConnect.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KilledHarmonic
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KilledKernelPow
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# R7 Fact B via Doeblin: the renewal-alignment connection to `erdos_partition_limit_exists`

The correct (satisfiable) Hardy–Ramanujan reduction.  Instantiates `tendsto_of_renewal_alignment` for the
concrete killed Erdős kernel: if the **renewal-alignment** holds for cofinitely many cutoffs `J` — the
`m`-step terminal laws of any two high-rank starts overlap by `≥ 1 − (1−δ)^m − ε` — then the normalized
partition sequence `u` converges to a positive limit.  Unlike the all-pairs single-step overlap (which is
false for far-rank pairs), the alignment input is genuinely satisfiable: two descending chains synchronize
at the shared lower rank levels they both pass through.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The **renewal-alignment** at cutoff `J`: for some `δ>0`, the `m`-step terminal laws of any two
high-rank starts overlap by `≥ 1 − (1−δ)^m − ε`. -/
def ErdosAlignment (J : ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
    ∀ (m : ℕ) (ε : ℝ), 0 < ε → ∃ R₀ : ℕ, ∀ i j, R₀ ≤ rnk i → R₀ ≤ rnk j →
      1 - (1 - δ) ^ m - ε ≤ ∑ k ∈ Finset.range (max i j + 1),
          min (KPowK m (killedKer Pker rnk J) i k) (KPowK m (killedKer Pker rnk J) j k)

end AnalyticCombinatorics.Ch8.Partitions.Erdos


