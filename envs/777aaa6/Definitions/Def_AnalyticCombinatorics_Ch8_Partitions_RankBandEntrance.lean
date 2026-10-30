-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RankBandEntrance
-- name    : AnalyticCombinatorics_Ch8_Partitions_RankBandEntrance
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:57:20.441728+00:00
-- url     : https://prove2.me/theorems/e45df12d-0438-485a-a1c5-88a1cf01ff79
-- title:
--   Rank Band Entrance
-- statement:
--   The source-linked mathematical setting supplies the finite-kernel, rank, moment, renewal or sequence models used by the exact support contracts in this group. The literal model declarations, where catalogued below, retain their source parameters and assumptions. Definition prose must be refined against the actual complete compiler-derived owner before an upload payload is prepared.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/RankBandEntrance.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# TASK 11: the first-entrance (run-until-hit) rank-band Doeblin engine

The fixed-step-count overlap reductions (`ErdosAlignment`, `DoeblinWalls`) are *false* for far-apart
high ranks (rank drops by `O(1)` per step, so a rank-`1000R` chain and a rank-`1001R` chain have
disjoint `L`-step laws for any fixed `L`).  This file builds the correct
device: the **first-entrance kernel** `enterBandKer P B`, which runs the chain *until* it enters a
finite rank band `B` — variable hitting time, not a fixed step count.  Two chains starting from very
different heights both descend *through* the band, and their first-entrance laws overlap.

Steps A–D (this file) are deterministic and reuse the banked Doeblin contraction
(`doeblin_average_diff_bound`) and the banked tail-oscillation engine (`tailOsc`,
`tendsto_zero_of_step_contraction`, `tendsto_of_tail_osc_to_zero`); they do **not** depend on the
hard analytic overlap sublemma (Step E).  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-! ## Step A — the first-entrance kernel -/

/-- **First-entrance kernel.**  `enterBandKer P B n z` is the probability that a `P`-chain started at
`n`, run until it first enters the finite set `B`, lands at `z`.  If `n ∈ B` the chain is already in
the band (point mass at `n`); otherwise it takes one `P`-step to a predecessor `k < n` and
continues.  Well-founded on `k < n` (same structure as `hitVal`, since `P n k` is summed over
`Finset.range n`). -/
noncomputable def enterBandKer (P : ℕ → ℕ → ℝ) (B : Finset ℕ) : ℕ → ℕ → ℝ
  | n =>
    if n ∈ B then (fun z => if z = n then 1 else 0)
    else (fun z => ∑ k ∈ (Finset.range n).attach, P n k.1 * enterBandKer P B k.1 z)
  termination_by n => n
  decreasing_by exact Finset.mem_range.mp k.2

variable {P : ℕ → ℕ → ℝ} {B : Finset ℕ}

/-! ## Step B — the entrance decomposition for `hitVal` -/

/-! ## Step C — Doeblin contraction of the entrance average (wires `doeblin_average_diff_bound`) -/

/-! ## Step D — the descending-ceiling band and the abstract engine

The *band* used by the engine is the **finite ceiling down-set** `ceilBand R A` = all states of rank
`< R + A` (truncated to the recursion's finite range).  This set is **unskippable on the way down**
(the chain can only enter it, never jump over it from above), so the first-entrance decomposition
holds with the harmonic hypothesis discharged at every off-band point (rank `≥ R + A ≥ J`).  The
landed point's rank is `< R + A`; the engine then splits the band into the in-band overlap part
`[R, R+A)` and the **overshoot** part `[0, R)`, which carries an escape mass driving the residual
oscillation.  A *fixed* band width `A` leaves a non-vanishing
escape floor (the genuine obstruction). -/


end AnalyticCombinatorics.Ch8.Partitions.Erdos


