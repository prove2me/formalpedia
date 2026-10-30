-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.tendsto_of_comparable_contraction
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:49:14.032168+00:00
-- url     : https://prove2.me/submissions/474c48ff-217d-4635-8973-95172f6168e4

import Mathlib

namespace AnalyticCombinatorics end AnalyticCombinatorics
namespace AnalyticCombinatorics.Ch8 end AnalyticCombinatorics.Ch8
namespace AnalyticCombinatorics.Ch8.Partitions end AnalyticCombinatorics.Ch8.Partitions
namespace AnalyticCombinatorics.Ch8.Partitions.Erdos end AnalyticCombinatorics.Ch8.Partitions.Erdos

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

/-!
# R7 Fact B via Doeblin: comparable-pair contraction ⟹ convergence (center-tracking packaging)

The far-pair obstruction is resolved by center-tracking: it suffices to control *comparable*-rank
oscillation (block centers `c` and a block-oscillation bound `V`), with far pairs handled by the
summable center links.  This lemma packages `tendsto_of_center_tracking` into the form produced by the
windowed-coupling ITER: a summable block-oscillation bound `V → 0` with `|h n − c(rank n)| ≤ V(rank n)`
(tracking) and adjacent centers `|c(R+1) − c R| ≤ V R` forces `h` to converge.  Opus-authored.
-/

noncomputable section

open Filter Topology

end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Filter Topology
theorem solution {h c V : ℕ → ℝ} {rank : ℕ → ℕ}
    (hrank : Tendsto rank atTop atTop)
    (hVtend : Tendsto V atTop (𝓝 0))
    (hVsum : Summable V)
    (htrack : ∀ n, |h n - c (rank n)| ≤ V (rank n))
    (hlink : ∀ R, |c (R + 1) - c R| ≤ V R) :
    ∃ L : ℝ, Tendsto h atTop (𝓝 L) := by
  refine tendsto_of_center_tracking hVtend ?_ htrack hrank
  exact Summable.of_nonneg_of_le (fun R => abs_nonneg _) hlink hVsum
