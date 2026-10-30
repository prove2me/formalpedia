-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Glaisher_glaisher_log_asymptotic
-- name    : AnalyticCombinatorics.Ch8.Partitions.Glaisher.glaisher_log_asymptotic
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:35:56.832803+00:00
-- url     : https://prove2.me/theorems/59986736-3621-44b1-83b5-e86eeeb5450f
-- title:
--   Logarithmic growth of restricted partition counts
-- statement:
--   Fix an integer $m\ge2$. Let $r_m(n)$ be the number of partitions of $n$ whose parts are not divisible by $m$, defined by the source restricted-partition finite type. Then $$\lim_{n\to\infty}\frac{\log r_m(n)}{\sqrt n}=\pi\sqrt{\frac23\left(1-\frac1m\right)}.$$ This is logarithmic growth, without a multiplicative asymptotic or an error rate.
--
--   The local source models, scales or predicates are defined exactly by:
--
--   ```lean
--   noncomputable def rpart (m n : ℕ) : ℝ :=
--     ((Nat.Partition.restricted n (fun k => ¬ m ∣ k)).card : ℝ)
--   ```
--
--   ```lean
--   noncomputable def cpart (m n : ℕ) : ℝ :=
--     (Fintype.card {p : Nat.Partition n // ∀ k ∈ p.parts, p.parts.count k < m} : ℝ)
--   ```
--
--   ```lean
--   noncomputable def Kglaisher (m : ℕ) : ℝ :=
--     (1 - 1 / (m : ℝ)) * A
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/GlaisherAsymptotic.lean#L830. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_GlaisherAsymptotic
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Glaisher

open Filter
open scoped BigOperators Topology Asymptotics

-- This file reuses the partition Tauberian pipeline with a finite `Fin m`
-- multiplicity model; the terminal finite-product and constant algebra proofs
-- need the same local heartbeat headroom as the distinct-parts file.
set_option maxHeartbeats 800000

/-! ### Finite count-restricted products -/

/-! ### Log-Laplace asymptotic -/

/-! ### Monotone transfer from cumulative sums to coefficients -/

theorem AnalyticCombinatorics.Ch8.Partitions.Glaisher.glaisher_log_asymptotic (m : ℕ) (hm : 2 ≤ m) :
    Tendsto (fun n : ℕ => Real.log (rpart m n) / Real.sqrt n) atTop
      (𝓝 (Real.pi * Real.sqrt (2 * (1 - 1 / (m : ℝ)) / 3))) := by sorry
