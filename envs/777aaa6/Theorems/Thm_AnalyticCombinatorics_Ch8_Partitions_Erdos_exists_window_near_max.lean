-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_exists_window_near_max
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.exists_window_near_max
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:48:24.853265+00:00
-- url     : https://prove2.me/theorems/c792e530-1097-4407-9f45-04e77d4ec3ef
-- title:
--   A near-record window with explicit defect terms
-- statement:
--   Near-record pullback with explicit defect terms and window/prefix hypotheses. No summability of those defects or all-record covering follows solely from this lemma.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem exists_window_near_max {a b μ M : ℝ} {N N₀ : ℕ} (hN2 : 2 ≤ N) (hμ : 0 < μ)
--       (hMnonneg : 0 ≤ M)
--       (hMbound : ∀ k : ℕ, k ≤ N → u k ≤ M)
--       (hmax : ∀ k : ℕ, N₀ ≤ k → k ≤ N → u k ≤ u N)
--       (hwin : μ ≤ kernelWindow a b N)
--       (hprefix : ∀ m : ℕ, m ∈ Finset.Icc 1 (N - 1) → ¬ (N₀ ≤ N - m) → N < 2 * m) :
--       ∃ m : ℕ, m ∈ Finset.Icc 1 (N - 1) ∧
--         (a * Real.sqrt (N : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (N : ℝ)) ∧
--         u N - (|boundaryTerm N| + M * |kernelMass N - 1|
--           + M * ((N : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (N : ℝ)))) / μ ≤ u (N - m)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/RecordPullback.lean#L31. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Mathlib

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Close end AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Mass-rate campaign: §8 the record pullback with summable defect (R7 core)

ChatGPT-Pro consult (task 19e127f1) established that the intended record-cover lemmas are NOT
derivable from boundedness + forward-fill + `b(n)→0` alone (explicit slowly-oscillating
countermodel).  The honest route needs the **one-step pullback with a quantitative defect**

  `Δ_N = (|b(N)| + M·|S_N − 1| + M·prefixTail(N)) / μ`,

summable on the `t = √n` scale for the genuine partition kernel.  This file banks the exact
one-step pullback (running-max version).  Opus-authored.
-/

set_option maxHeartbeats 1000000

open Filter Finset
open scoped BigOperators Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.exists_window_near_max {a b μ M : ℝ} {N N₀ : ℕ} (hN2 : 2 ≤ N) (hμ : 0 < μ)
    (hMnonneg : 0 ≤ M)
    (hMbound : ∀ k : ℕ, k ≤ N → u k ≤ M)
    (hmax : ∀ k : ℕ, N₀ ≤ k → k ≤ N → u k ≤ u N)
    (hwin : μ ≤ kernelWindow a b N)
    (hprefix : ∀ m : ℕ, m ∈ Finset.Icc 1 (N - 1) → ¬ (N₀ ≤ N - m) → N < 2 * m) :
    ∃ m : ℕ, m ∈ Finset.Icc 1 (N - 1) ∧
      (a * Real.sqrt (N : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (N : ℝ)) ∧
      u N - (|boundaryTerm N| + M * |kernelMass N - 1|
        + M * ((N : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (N : ℝ)))) / μ ≤ u (N - m) := by sorry
