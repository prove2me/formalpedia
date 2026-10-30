-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_erdos_partition_limit_constant
-- name    : AnalyticCombinatorics.Ch8.Partitions.erdos_partition_limit_constant
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:40:36.047021+00:00
-- url     : https://prove2.me/theorems/d458a8de-248d-415a-84da-c6c96f6e51e2
-- title:
--   Exact normalized limit for integer partition counts
-- statement:
--   Let $p(n)$ be the real-valued cardinality of the finite type of unordered partitions of the natural number $n$ into positive integer parts. Put $C=\pi\sqrt{2/3}$ and
--
--   $$u_n=n\,p(n)\exp(-C\sqrt n).$$
--
--   Then
--
--   $$\lim_{n\to\infty}u_n=\frac{1}{4\sqrt3}.$$
--
--   In particular, this positive limiting normalization corresponds to
--
--   $$p(n)\sim\frac{\exp(\pi\sqrt{2n/3})}{4n\sqrt3}.$$
--
--   The exact formal conclusion is the real convergence of $u_n$ to $1/(4\sqrt3)$; its additive error is $o(1)$, with no quantitative error rate supplied. There are no public parameters or hypotheses in the selected source theorem: the required existence of a positive limit and its constant identification are obtained from earlier source theorems. The normalized sequence uses the actual partition cardinalities and has $u_0=0$; the assertion concerns $n\to\infty$, not a finite-index formula.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/ErdosHRConstant.lean#L26. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# The complete Hardy–Ramanujan partition limit (with the exact constant)

`Erdos.erdos_partition_limit_exists` (CeilingEscapeClose) proves the normalized partition sequence
`u n = n · p(n) · exp(−C√n)` (`C = π√(2/3)`) converges to *some* positive limit.
`erdos_limit_constant_of_renewal` (ErdosRiemannError) forces that limit to equal `1/(4√3)`,
unconditionally (the mesh-1 Riemann error is negligible, `riemannError_negligible`).

This file assembles the two into the full Hardy–Ramanujan statement
`u n → 1/(4√3)`, the leading-order partition asymptotic `p(n) ~ exp(π√(2n/3)) / (4n√3)`.
-/

open Filter Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions

theorem AnalyticCombinatorics.Ch8.Partitions.erdos_partition_limit_constant :
    Tendsto Erdos.u atTop (𝓝 (1 / (4 * Real.sqrt 3))) := by sorry
