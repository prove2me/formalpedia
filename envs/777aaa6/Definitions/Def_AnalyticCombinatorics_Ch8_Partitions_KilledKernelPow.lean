-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KilledKernelPow
-- name    : AnalyticCombinatorics_Ch8_Partitions_KilledKernelPow
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:53:33.349109+00:00
-- url     : https://prove2.me/theorems/b7b09dd8-d748-4c71-bd9e-1f369305aad8
-- title:
--   Killed Kernel Pow mathematical objects
-- statement:
--   Finite downward-kernel composition and its natural iterates are defined explicitly, with the zeroth power equal to the identity kernel.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/KilledKernelPow.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# R7 Fact B via Doeblin (killed kernel): boundary-absorbing kernel powers

The killed kernel `P̃` (predecessor steps above the cutoff, identity-absorb on the boundary) has
support `k ≤ n` (predecessor OR diagonal), so its composition sums over `range (n+1)`.  This file
builds `KCompK`/`KPowK` and proves nonnegativity and the support `n < k → · = 0`.  The `L`-fold killed
power is the law used in the Doeblin pairwise contraction for the exactly-harmonic `hitVal`.
Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Killed-kernel composition (sum over `range (n+1)`, allowing the diagonal). -/
def KCompK (P Q : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun n k => ∑ j ∈ Finset.range (n + 1), P n j * Q j k

/-- `L`-fold killed-kernel power; `KPowK 0` is the identity kernel `δ(k=n)`. -/
def KPowK : ℕ → (ℕ → ℕ → ℝ) → ℕ → ℕ → ℝ
  | 0, _ => fun n k => if k = n then 1 else 0
  | L + 1, P => KCompK P (KPowK L P)

end AnalyticCombinatorics.Ch8.Partitions.Erdos


