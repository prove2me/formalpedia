-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_partition_log_isEquivalent
-- name    : AnalyticCombinatorics.Ch8.Partitions.partition_log_isEquivalent
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-25T13:51:21.917099+00:00
-- url     : https://prove2.me/theorems/92362cd0-5010-4bee-ae47-67bb3355f4be
-- title:
--   Logarithmic growth of integer partition counts
-- statement:
--   For a natural number $n$, let $p(n)$ be the cardinality of the finite type of unordered partitions of $n$ into positive integer parts, viewed as a real number. Thus $p(0)=1$ and $p(n)>0$. Then
--
--   $$\log p(n)\sim \pi\sqrt{\frac{2n}{3}}\qquad(n\to\infty).$$
--
--   The logarithm is the real natural logarithm and the square root is the nonnegative real square root. The displayed asymptotic equivalence means that the quotient tends to $1$; its comparison is eventually positive. Equivalently, the logarithmic error is $o(\sqrt n)$. No smaller error rate or multiplicative asymptotic for $p(n)$ is asserted by this target alone. The selected source theorem has no public parameters or assumptions, with its Laplace and Tauberian inputs supplied by earlier source theorems. The claim is eventual and is not a quotient identity at $n=0$.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/LogAsymptotic.lean#L213. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions

open Filter
open scoped BigOperators Topology Asymptotics

-- The final transfer combines real logarithm/square-root limits with field
-- simplification; this keeps those terminal proofs within the local file.
set_option maxHeartbeats 400000

theorem AnalyticCombinatorics.Ch8.Partitions.partition_log_isEquivalent :
    (fun n : ℕ => Real.log (part n)) ~[atTop]
      (fun n : ℕ => Real.pi * Real.sqrt (2 * (n : ℝ) / 3)) := by sorry
