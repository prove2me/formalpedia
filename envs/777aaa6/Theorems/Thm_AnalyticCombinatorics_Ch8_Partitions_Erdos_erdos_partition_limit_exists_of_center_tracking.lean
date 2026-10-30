-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdos_partition_limit_exists_of_center_tracking
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.erdos_partition_limit_exists_of_center_tracking
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:58:11.509405+00:00
-- url     : https://prove2.me/theorems/86f6fce1-4e3a-4d7f-bf88-f206f1e7caa2
-- title:
--   A conditional partition-limit reduction from center tracking
-- statement:
--   Let $u_n=n\,\texttt{part}(n)\exp(-C\sqrt n)$, with the source partition count and $C=\pi\sqrt{2/3}$. The source kernel, rank and killed hit-value constructions are those defined below. Assume that for all sufficiently large cutoffs $J$ there exist functions $c,V:\mathbb N\to\mathbb R$ such that $V(R)\to0$, $\sum_R|c(R+1)-c(R)|<\infty$, and $$|\texttt{hitVal}(P_{\rm ker},\texttt{rnk},J,u,n)-c(\texttt{rnk}(n))|\le V(\texttt{rnk}(n))\quad\text{for every }n.$$ Then $$\exists a>0,\quad u_n\longrightarrow a.$$ This implication retains the entire tracking hypothesis; it does not construct its witnesses.
--
--   This conditional reduction carries the following complete literal source contract:
--
--   ```lean
--   theorem erdos_partition_limit_exists_of_center_tracking
--       (hdata : ∀ᶠ J : ℕ in atTop,
--           ∃ c V : ℕ → ℝ,
--             Tendsto V atTop (𝓝 0) ∧
--             Summable (fun R => |c (R + 1) - c R|) ∧
--             (∀ n, |hitVal Pker rnk J u n - c (rnk n)| ≤ V (rnk n))) :
--       ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/CenterTrackingHitVal.lean#L47. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RenewalHitPot
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
# hhit via center-tracking: the gap-isolating interface

This is a *structural* brick, NOT a closure of `hhit`.  It packages the §9 convergence engine
`tendsto_of_center_tracking` for the concrete killed-harmonic hit value `hitVal Pker rnk J u`, so that
the remaining analytic content is exactly the explicit hypothesis `hdata`:

  for cofinitely many cutoffs `J`, there exist a center sequence `c` and a tracking bound `V` with
  * `V → 0`                         (the *tracking* error — may be only polynomial, e.g. `R^{-1/2}`),
  * `∑_R |c(R+1) − c R| < ∞`        (the *center links* — must be summable), and
  * `|hitVal_J(n) − c(rnk n)| ≤ V(rnk n)`.

The design audit (ChatGPT R1/R2, 2026-06-13) established that the coupling/FK route supplies the
*tracking* bound at a polynomial (non-summable) rate, while the *summable center links* require a
separate finite-boundary renewal / kernel-gradient estimate that is NOT derivable from the banked
first-moment drift `muTilde_two_term`.  This interface isolates that single remaining input.
-/

open Filter Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.erdos_partition_limit_exists_of_center_tracking
    (hdata : ∀ᶠ J : ℕ in atTop,
        ∃ c V : ℕ → ℝ,
          Tendsto V atTop (𝓝 0) ∧
          Summable (fun R => |c (R + 1) - c R|) ∧
          (∀ n, |hitVal Pker rnk J u n - c (rnk n)| ≤ V (rnk n))) :
    ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a) := by sorry
