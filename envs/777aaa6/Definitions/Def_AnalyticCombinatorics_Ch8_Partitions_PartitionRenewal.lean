-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
-- name    : AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:08:07.8904+00:00
-- url     : https://prove2.me/theorems/7ca974a6-5074-4c9b-9950-e5f0914b5e88
-- title:
--   Partition Renewal mathematical objects
-- statement:
--   Pker(n,k) is the normalized recurrence weight for1≤k<n and zero elsewhere. The rank is floor(3sqrt(n)); the residual dres(n) subtracts the finite kernel-weighted earlier values from u(n).
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/PartitionRenewal.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# R7 Layer 1: instantiation of the renewal spine to the partition kernel

Defines the predecessor transition kernel `Pker n k = erdosWeight n (n−k)/kernelMass n`, the rank
`rnk n = ⌊3√n⌋` (`ρ=3` makes window steps strictly drop rank), and the residual `dres`.  Proves the
kernel facts that feed the banked spine (`rec_iter_bound`, `pot_le_block_sum_of_leave`): nonnegativity,
rank monotonicity, the recurrence-in-`P` form, the probability normalization, the residual bound
(block-summable via `DefectSummable`), and the leave-probability `≥ μ`.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Predecessor transition kernel `P n k = erdosWeight n (n−k)/kernelMass n` for `1 ≤ k < n`. -/
noncomputable def Pker (n k : ℕ) : ℝ :=
  if 1 ≤ k ∧ k < n then erdosWeight n (n - k) / kernelMass n else 0

/-- Rank on the `√n` scale: `⌊3√n⌋` (the factor `3 > 2/α` forces window steps to drop rank). -/
noncomputable def rnk (n : ℕ) : ℕ := ⌊3 * Real.sqrt (n : ℝ)⌋₊

end AnalyticCombinatorics.Ch8.Partitions.Erdos


