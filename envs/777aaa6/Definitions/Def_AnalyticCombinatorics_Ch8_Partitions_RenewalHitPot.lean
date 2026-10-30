-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RenewalHitPot
-- name    : AnalyticCombinatorics_Ch8_Partitions_RenewalHitPot
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T18:53:22.388993+00:00
-- url     : https://prove2.me/theorems/02b600c4-c8f6-47af-9cd5-be16e8bc401c
-- title:
--   Renewal Hit Pot mathematical objects
-- statement:
--   Given a kernel $P:\mathbb N\to\mathbb N\to\mathbb R$, a rank function, a cutoff $J$ and boundary values $\varphi$, `hitVal P rank J φ` is defined by well-founded recursion on $n$: if $\mathrm{rank}(n)<J$ its value is $\varphi(n)$, and otherwise it is $\sum_{k<n} P(n,k)\,\mathrm{hitVal}(k)$, the $P$-weighted sum of its values at smaller arguments. It is the value at first entry below the rank cutoff.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/RenewalHitPot.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# R7 renewal route: well-founded `Hit`/`Pot` potentials

The banked spine lemmas (`rec_iter_bound`, `pot_le_block_sum_of_leave`) take the `Hit`/`Pot`
fixed-point equations as hypotheses.  This file constructs the actual functions by well-founded
recursion on `n` (the kernel `P n k` is summed over `Finset.range n`, so every recursive call is on
`k < n`).  We sum over `(Finset.range n).attach` so each summand carries the membership proof
`k ∈ range n` (hence `k < n`) needed for termination, then recover the plain-`range` defining
equations via `Finset.sum_attach`.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Harmonic extension to the cutoff: `Hit J φ n = φ n` below the cutoff `rank n < J`, else the
`P`-average of `Hit` over predecessors. -/
noncomputable def hitVal (P : ℕ → ℕ → ℝ) (rank : ℕ → ℕ) (J : ℕ) (φ : ℕ → ℝ) : ℕ → ℝ
  | n =>
    if rank n < J then φ n
    else ∑ k ∈ (Finset.range n).attach, P n k.1 * hitVal P rank J φ k.1
  termination_by n => n
  decreasing_by exact Finset.mem_range.mp k.2

end AnalyticCombinatorics.Ch8.Partitions.Erdos


