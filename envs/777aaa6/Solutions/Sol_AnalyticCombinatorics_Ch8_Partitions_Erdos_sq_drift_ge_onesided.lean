-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.sq_drift_ge_onesided
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:28:04.505071+00:00
-- url     : https://prove2.me/submissions/0a2faf67-2298-4547-bd05-eebfa40319ef

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_QVTelescope
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
/-!
# R7 Fact B via Doeblin: η-robust lower quadratic variation

For an η-approximate martingale (`|∑ K x z · D z − D x| ≤ η`), the second-moment drift is
`locVar x + 2·D x·e` with `e = ∑ K x z D z − D x` the drift error; since `2 D x e ≥ −2Rη` (where
`|D| ≤ R`), telescoping gives

  `E[D_T²] ≥ E[D_0²] + (v₀ − 2Rη)·T`.

With `η ~ 1/r²` and `R ~ r`, the correction `2Rη ~ 1/r → 0`, so the effective variance `v₀ − 2Rη → v₀`
and the lower QV survives.  Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- Unconditional second-moment drift identity (no martingale needed). -/
lemma sq_drift_id (K : ι → ι → ℝ) (D : ι → ℝ) (x : ι) (hKsum : ∑ z, K x z = 1) :
    (∑ z, K x z * (D z) ^ 2) - (D x) ^ 2
      = locVar K D x + 2 * (D x) * ((∑ z, K x z * D z) - D x) := by
  unfold locVar
  have hexp : ∀ z, K x z * (D z - D x) ^ 2
      = K x z * (D z) ^ 2 - (2 * D x) * (K x z * D z) + (D x) ^ 2 * K x z := fun z => by ring
  rw [Finset.sum_congr rfl (fun z _ => hexp z), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hKsum]
  ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# R7 Fact B via Doeblin: one-sided (localized) lower quadratic variation

For the *conditioned* residual walk `K̂res`, the drift is NOT uniformly small: on-window it is a bounded
REPELLING drift (`D·e ≥ 0`), off-window it is the product drift (`|e| ≤ η`).  The energy/QV lower bound
needs only the ONE-SIDED bound `D x · (∑ K x z D z − D x) ≥ −R·η` (which holds in both regimes: off-window
`≥ −Rη`, on-window `≥ 0`), so the lower quadratic variation `E[D_T²] ≥ E[D_0²] + (v₀ − 2Rη)·T` survives
without uniform mart-eta.  This is the localization needed to apply the occupation argument to the
conditioned walk.  Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
theorem solution {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (D : ι → ℝ) (v0 η R : ℝ) (x : ι)
    (hKsum : ∑ z, K x z = 1) (hlvge : v0 ≤ locVar K D x)
    (hcross : -(R * η) ≤ (D x) * ((∑ z, K x z * D z) - D x)) :
    v0 - 2 * R * η ≤ (∑ z, K x z * (D z) ^ 2) - (D x) ^ 2 := by
  rw [sq_drift_id K D x hKsum]; linarith [hlvge, hcross]
