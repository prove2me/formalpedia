-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_GlaisherAsymptotic
-- name    : AnalyticCombinatorics_Ch8_Partitions_GlaisherAsymptotic
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:34:10.575738+00:00
-- url     : https://prove2.me/theorems/92e8ad7c-9638-4329-950f-7be4ed9c9790
-- title:
--   Glaisher Asymptotic
-- statement:
--   The source mathematical objects and operations are specified by the following definitions.
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
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/GlaisherAsymptotic.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Glaisher

open Filter
open scoped BigOperators Topology Asymptotics

-- This file reuses the partition Tauberian pipeline with a finite `Fin m`
-- multiplicity model; the terminal finite-product and constant algebra proofs
-- need the same local heartbeat headroom as the distinct-parts file.
set_option maxHeartbeats 800000

/-- The genuine number of partitions of `n` whose parts are not divisible by `m`,
as a real number. -/
noncomputable def rpart (m n : ℕ) : ℝ :=
  ((Nat.Partition.restricted n (fun k => ¬ m ∣ k)).card : ℝ)

/-! ### Finite count-restricted products -/

/-! ### Log-Laplace asymptotic -/

/-! ### Monotone transfer from cumulative sums to coefficients -/

end AnalyticCombinatorics.Ch8.Partitions.Glaisher


