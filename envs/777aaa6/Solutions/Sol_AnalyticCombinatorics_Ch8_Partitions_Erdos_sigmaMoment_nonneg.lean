-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.sigmaMoment_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:19:26.523387+00:00
-- url     : https://prove2.me/submissions/edc79814-639e-46da-90ed-7327218259a9

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
namespace AnalyticCombinatorics.Ch8.Partitions.Sigma

open scoped BigOperators

lemma sigmaR_eq_sum_divisors (m : ℕ) :
    sigmaR m = ∑ d ∈ m.divisors, (d : ℝ) := by
  rw [sigmaR, ArithmeticFunction.sigma_one_apply]
  norm_num

end AnalyticCombinatorics.Ch8.Partitions.Sigma
end

section
namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open Filter
open scoped BigOperators Topology

noncomputable section

lemma sigmaR_nonneg (n : ℕ) : 0 ≤ Sigma.sigmaR n := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  exact Finset.sum_nonneg fun d _hd => by positivity

end
end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

/-!
# MuNum two-term expansion

`|muNum n − (μ̄ + μA/√n)| ≤ K/n` for large `n`, where
`μ̄ = 3/massLam` and `μA = 3/(2·massLam²)`.
-/

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-! ### Algebraic expansion of the model product -/

/-! ### Model sum expressed via sigma moments (infinite-sum identity) -/

/-! ### Small lemmas -/

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
set_option maxHeartbeats 4000000
open Filter Finset
open scoped Topology BigOperators
theorem solution (r : ℕ) (t : ℝ) (ht : 0 < t) : 0 ≤ sigmaMoment r t := by
  rw [sigmaMoment]
  refine tsum_nonneg (fun m => ?_)
  rcases eq_or_ne m 0 with h | h
  · simp [h]
  · rw [if_neg h]
    have hσ : 0 ≤ Sigma.sigmaR m := sigmaR_nonneg m
    positivity
