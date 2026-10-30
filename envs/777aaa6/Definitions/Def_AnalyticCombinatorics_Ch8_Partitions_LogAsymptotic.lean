-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_LogAsymptotic
-- name    : AnalyticCombinatorics_Ch8_Partitions_LogAsymptotic
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T13:49:32.87884+00:00
-- url     : https://prove2.me/theorems/4011ca4b-4c37-4f23-9a25-3248f8761b66
-- title:
--   Log Asymptotic mathematical objects
-- statement:
--   PartCum(N) is the cumulative partition count sum of part(n) from n=0 through N, inclusive. Given natural m<=n, addOnesPartition maps a partition of m to a partition of n by adjoining n-m parts equal to 1.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/LogAsymptotic.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_Tauberian
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


namespace AnalyticCombinatorics.Ch8.Partitions

open Filter
open scoped BigOperators Topology Asymptotics

-- The final transfer combines real logarithm/square-root limits with field
-- simplification; this keeps those terminal proofs within the local file.
set_option maxHeartbeats 400000

noncomputable def PartCum (N : ℕ) : ℝ :=
  Tauberian.Cum part N

def addOnesPartition {m n : ℕ} (hmn : m ≤ n) (p : Nat.Partition m) :
    Nat.Partition n where
  parts := p.parts + Multiset.replicate (n - m) 1
  parts_pos := by
    intro i hi
    rw [Multiset.mem_add] at hi
    rcases hi with hi | hi
    · exact p.parts_pos hi
    · have h : i = 1 := Multiset.eq_of_mem_replicate hi
      omega
  parts_sum := by
    rw [Multiset.sum_add, Multiset.sum_replicate, p.parts_sum]
    simp
    omega

end AnalyticCombinatorics.Ch8.Partitions


