-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.erdos_partition_limit_exists_of_center_tracking
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:59:04.024977+00:00
-- url     : https://prove2.me/submissions/5684ff41-472a-4f8f-ba24-5d514e8bce30

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RenewalHitPot
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdos_partition_limit_exists_of_hit
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
/-!
# R7 Fact B via Doeblin: the §9 convergence engine

The deterministic core of the block-oscillation → convergence connection.  If the tail-sup of block
oscillation `V` is summable, the block-centers `c` have summable consecutive links (`|c(R+1)−c R| ≤
V R`) hence converge to some `L`, and `h` tracks the centers (`|h n − c(rank n)| ≤ V(rank n) → 0`), so
`h → L`.  This avoids the far-pair overlap obstruction entirely: only the *monotone* tail-sup `V`
needs to contract (geometrically), which it does because the local contraction dominates it.
Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **§9 convergence engine.** Summable tail-sup `V` + center links + center-tracking ⟹ `h` converges. -/
theorem tendsto_of_center_tracking {h c V : ℕ → ℝ} {rank : ℕ → ℕ}
    (hVtend : Tendsto V atTop (𝓝 0))
    (hlink_sum : Summable (fun R => |c (R + 1) - c R|))
    (htrack : ∀ n, |h n - c (rank n)| ≤ V (rank n))
    (hrank : Tendsto rank atTop atTop) :
    ∃ L : ℝ, Tendsto h atTop (𝓝 L) := by
  -- centers are Cauchy: consecutive distances are summable
  have hdist_sum : Summable (fun R => dist (c R) (c (R + 1))) := by
    simpa [Real.dist_eq, abs_sub_comm] using hlink_sum
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist_sum)
  refine ⟨L, ?_⟩
  have h1 : Tendsto (fun n => c (rank n)) atTop (𝓝 L) := hL.comp hrank
  have h2 : Tendsto (fun n => h n - c (rank n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (hVtend.comp hrank)
    simpa [Real.norm_eq_abs] using htrack n
  have hsum := h1.add h2
  simpa using hsum

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: concrete facts about `rnk` and `kernelMass`

Two elementary facts needed to instantiate the abstract `tendsto_of_killed_doeblin` for the concrete
Erdős predecessor kernel: the rank map `rnk n = ⌊3√n⌋` diverges (`rnk → atTop`), and the kernel mass
`kernelMass n` is eventually strictly positive (it dominates the window mass, which is `≥ ν > 0`
eventually).  The latter makes `Pker` row-stochastic for large `n` (via `Pker_mass`).  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The rank map diverges: `rnk n = ⌊3√n⌋ → ∞`. -/
lemma rnk_tendsto_atTop : Tendsto rnk atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨(b + 1) ^ 2, fun n hn => ?_⟩
  have h1 : ((b + 1) ^ 2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb_le_sqrt : (b : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [show (b : ℝ) = Real.sqrt ((b : ℝ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [h1, (Nat.cast_nonneg b : (0:ℝ) ≤ (b:ℝ))]
  have hsqrt : (b : ℝ) ≤ 3 * Real.sqrt (n : ℝ) := by
    have := Real.sqrt_nonneg (n : ℝ); linarith
  unfold rnk
  exact Nat.le_floor hsqrt

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

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

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **`hhit` from eventual center-tracking of `hitVal`.**  If, for cofinitely many cutoffs `J`, the
killed-harmonic hit value tracks a center sequence with a vanishing error and summable center links,
then `hitVal Pker rnk J u` converges for cofinitely many `J` (i.e. `hhit` holds).  Immediate from
`tendsto_of_center_tracking`; the content is entirely in `hdata`. -/
theorem hhit_of_eventual_center_tracking_hitVal
    (hdata : ∀ᶠ J : ℕ in atTop,
        ∃ c V : ℕ → ℝ,
          Tendsto V atTop (𝓝 0) ∧
          Summable (fun R => |c (R + 1) - c R|) ∧
          (∀ n, |hitVal Pker rnk J u n - c (rnk n)| ≤ V (rnk n))) :
    ∀ᶠ J : ℕ in atTop,
        ∃ L : ℝ, Tendsto (fun n => hitVal Pker rnk J u n) atTop (𝓝 L) := by
  filter_upwards [hdata] with J hJ
  obtain ⟨c, V, hVtend, hlink, htrack⟩ := hJ
  exact tendsto_of_center_tracking hVtend hlink htrack rnk_tendsto_atTop

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Filter Topology
theorem solution
    (hdata : ∀ᶠ J : ℕ in atTop,
        ∃ c V : ℕ → ℝ,
          Tendsto V atTop (𝓝 0) ∧
          Summable (fun R => |c (R + 1) - c R|) ∧
          (∀ n, |hitVal Pker rnk J u n - c (rnk n)| ≤ V (rnk n))) :
    ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a) :=
  erdos_partition_limit_exists_of_hit (hhit_of_eventual_center_tracking_hitVal hdata)
