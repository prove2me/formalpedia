-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_Model_erdos_kernel_window
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.Model.erdos_kernel_window
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T15:32:05.354635+00:00
-- url     : https://prove2.me/theorems/8dcf459f-b771-4909-9aec-ad8d3cef7b92
-- title:
--   The true-kernel window limit
-- statement:
--   **The true-kernel window limit** (HR Stage I.3):
--
--     `Σ_{(a√n, b√n]} erdosWeight n m → ∫_a^b (π²/6) y e^{−(C/2)y} dy`.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem erdos_kernel_window {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
--       Tendsto
--         (fun n : ℕ => ∑ m ∈ Finset.Icc 1 (n - 1),
--           (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
--               (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
--            then erdosWeight n m else 0))
--         atTop (𝓝 (modelIntegral C a b))
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/KernelWindow.lean#L195. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ModelAssembly
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# The true-kernel window limit

`Σ_{(a√n, b√n]} erdosWeight n m → ∫_a^b (π²/6) y e^{−(C/2)y} dy`.

Conversion of the model kernel to the true Erdős kernel via the banked uniform window
replacements: `1/(n−m) = 1/n + O(b/n^{3/2})` (`inv_window_approx`) and
`√n − √(n−m) = m/(2√n) + O(b²/√n)·(1/√n)` (`sqrt_diff_window_approx`), with all
exponentials `≤ 1` on the window.  Per-term difference `≤ σ(m)·D/n^{3/2}`; summed against
the quadratic divisor bound `Σ_{m ≤ b√n} σ(m) ≤ B b² n` this is `O(1/√n) → 0`, and
`model_kernel_window` finishes.  Opus-authored.
-/

set_option maxHeartbeats 800000

open Filter Finset
open scoped BigOperators Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos AnalyticCombinatorics.Ch8.Partitions.Erdos.Model

local notation "σR" => Sigma.sigmaR

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.Model.erdos_kernel_window {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Tendsto
      (fun n : ℕ => ∑ m ∈ Finset.Icc 1 (n - 1),
        (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
         then erdosWeight n m else 0))
      atTop (𝓝 (modelIntegral C a b)) := by sorry
