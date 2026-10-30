-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
-- name    : AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:47:03.985332+00:00
-- url     : https://prove2.me/theorems/cfa38d8c-e3ed-4935-94d7-73a2d06ae750
-- title:
--   Kernel Barriers mathematical objects
-- statement:
--   For $n\in\mathbb N$, `kernelMass n` is the total recurrence-kernel mass $\sum_{m=1}^{n-1}\texttt{erdosWeight}(n,m)$, and for reals $a,b$, `kernelWindow a b n` is the same sum restricted to the indices with $a\sqrt n<m\le b\sqrt n$.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/KernelBarriers.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Barrier-package foundations (HR Stage I.5)

Definitions and the easy layers of the logarithmic-barrier route to two-sided boundedness
of `u` (route R6, audited): `kernelMass`/`kernelWindow`, the barriers `1 ∓ A/log(n+E)`,
the slack scale `1/(√n log²(n+E))`, the positive fixed window (from the banked
`erdos_kernel_window` + integral positivity), barrier range bounds, and boundary-vs-slack
negligibility (from the banked cube-decay lemma).  Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Total kernel mass. -/
noncomputable def kernelMass (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m

/-- Half-open window kernel mass `(a√n, b√n]`. -/
noncomputable def kernelWindow (a b : ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (n - 1),
    if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
    then erdosWeight n m else 0

end AnalyticCombinatorics.Ch8.Partitions.Erdos


