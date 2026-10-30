-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_muTilde_two_term
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.muTilde_two_term
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:32:26.210894+00:00
-- url     : https://prove2.me/theorems/a8b01b15-7c17-4253-94e9-d99d6174f27c
-- title:
--   Two-term smooth-rank drift expansion
-- statement:
--   For the source partition renewal kernel, write $\lambda=\texttt{massLam}$, $\rho(n,m)=3(\sqrt n-\sqrt{n-m})$, where $n-m$ is natural subtraction, and $$\widetilde\mu_n=\frac{\sum_{1\le m<n}\texttt{erdosWeight}(n,m)\rho(n,m)}{\texttt{kernelMass}(n)}.$$ There exists a real $K>0$ such that, for all sufficiently large natural $n$, $$\left|\widetilde\mu_n-\left(\frac3\lambda+\frac{3}{2\lambda^2\sqrt n}\right)\right|\le\frac K n.$$ This estimates the concrete kernel statistic; it does not supply any separate tracking or summability hypothesis.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean#L1062. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuTilde
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuTilde_x1
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

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.muTilde_two_term :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      |muTilde n - (3 / massLam + (3 / (2 * massLam ^ 2)) / Real.sqrt (n : ℝ))|
      ≤ K / (n : ℝ) := by sorry
