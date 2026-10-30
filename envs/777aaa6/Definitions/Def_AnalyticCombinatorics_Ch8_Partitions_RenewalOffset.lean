-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RenewalOffset
-- name    : AnalyticCombinatorics_Ch8_Partitions_RenewalOffset
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:05:36.106546+00:00
-- url     : https://prove2.me/theorems/20173468-b6e6-4649-ae1d-d814ebee9127
-- title:
--   Renewal Offset
-- statement:
--   The source-linked mathematical setting supplies the finite-kernel, rank, moment, renewal or sequence models used by the exact support contracts in this group. The literal model declarations, where catalogued below, retain their source parameters and assumptions. Definition prose must be refined against the actual complete compiler-derived owner before an upload payload is prepared.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/RenewalOffset.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# TASK T2.2: the overshoot/residual chain and its Doeblin coupling

The first-crossing offset of an integer renewal process is governed by the **residual chain**
(a.k.a. overshoot chain): the Markov chain on `ℕ` whose state is the current undershoot/residual
to the next ceiling.  Concretely, if the renewal increments have law `p` (supported on `{1,2,…}`),
the residual chain has transition

* from state `0` (just landed on the level): jump by an increment `d ∼ p`, leaving residual `d − 1`;
* from state `r+1` (residual `r+1` to the next level): deterministically step down to residual `r`.

So one *unit* of the level coordinate is one residual step.  The chain hits `0` exactly at renewal
epochs.  Crucially, the **stationary offset law** is the size-biased increment law, and two copies of
the residual chain from any two starting residuals couple by the Doeblin minorization coming from
`p 1 > 0` (an increment of `1` resets the residual to `0` regardless of the past).

This file builds the residual chain's one-step kernel `resStep`, its `n`-step kernel `resKer`,
the **return-to-zero-then-restart** structure, and the elementary facts (row-stochastic,
nonneg, support).  The Doeblin coupling / overlap + escape-tail conclusions are in
`RenewalOverlap.lean`.

Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Renewal

/-- **One-step residual kernel.**  `resStep p r r'` = probability that the residual chain moves from
state `r` to state `r'` in one *unit-level* step.

* From `0`: an increment `d = r' + 1 ∼ p` is drawn, leaving residual `r'` (so `resStep p 0 r' =
  p (r' + 1)`).
* From `r+1`: deterministic step down to `r` (so `resStep p (r+1) r' = [r' = r]`). -/
noncomputable def resStep (p : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun r' => p (r' + 1)
  | (r+1) => fun r' => if r' = r then 1 else 0

/-! ## Deterministic descent: the residual chain from `r+1` steps down to `r` with certainty. -/

/-! ## The increment-`1` minorization: an increment of `1` from residual `0` returns to `0`. -/

/-! ## The `n`-step residual kernel. -/

/-- `n`-step residual kernel.  `resKer p n r r'` = probability the residual chain moves from `r` to
`r'` in `n` unit-level steps. -/
noncomputable def resKer (p : ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0 => fun r r' => if r' = r then 1 else 0
  | (n+1) => fun r r' => ∑' m, resStep p r m * resKer p n m r'

@[simp] lemma resKer_zero (p : ℕ → ℝ) (r r' : ℕ) :
    resKer p 0 r r' = if r' = r then 1 else 0 := rfl


end AnalyticCombinatorics.Ch8.Partitions.Renewal


