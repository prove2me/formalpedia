-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.erdosWeight_nonneg_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:18:27.197463+00:00
-- url     : https://prove2.me/submissions/a5152c41-15c3-4024-88b6-e1d6854c735a

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
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

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open Filter
open scoped BigOperators Topology

noncomputable section

lemma sigmaR_nonneg (n : ℕ) : 0 ≤ Sigma.sigmaR n := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  exact Finset.sum_nonneg fun d _hd => by positivity

end
end AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Filter
open scoped BigOperators Topology
theorem solution {n m : ℕ} (hmn : m < n) :
    0 ≤ erdosWeight n m := by
  dsimp [erdosWeight]
  have hden : 0 < ((n - m : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hmn
  exact mul_nonneg (div_nonneg (sigmaR_nonneg m) hden.le) (Real.exp_pos _).le
