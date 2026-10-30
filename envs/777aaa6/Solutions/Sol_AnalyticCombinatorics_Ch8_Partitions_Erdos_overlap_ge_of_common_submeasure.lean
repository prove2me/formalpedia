-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.overlap_ge_of_common_submeasure
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:39:03.875817+00:00
-- url     : https://prove2.me/submissions/f5f2fc72-bf20-4bc7-9095-2ba3aaa84f1b

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# TASK T2-value, brick 2.0: the common-submeasure overlap bridge

The variable rank-band engine (`hitVal_cauchy_of_ceilBand_overlap_escape_variable`,
`RankBandEntrance.lean`) consumes a **value-level** overlap
`δ ≤ ∑_{z ∈ slice} min (κ n z) (κ n' z)`.  The banked `overlap_ge_of_minorization`
(`RenewalOverlap.lean`) derives this from a *single-state* minorization `κ n z ≥ η` on a fixed
finite set `S`, which is FALSE for a growing band (the first-entrance landing law spreads over the
whole band, so the per-state mass `max_z κ n z → 0`).

This brick generalizes that bridge: instead of a per-state floor, it consumes a *common submeasure*
`lam : ℕ → ℝ`, a nonnegative function dominated pointwise by *both* kernels on the slice, and
returns `∑ lam ≤ ∑ min`.  The common mass may be spread arbitrarily over the growing band; only its
total `∑ lam ≥ δ` needs to stay uniform.  Trivial: `min (κ n z) (κ n' z) ≥ lam z` pointwise on the
slice, then sum.

NEW file; imports nothing from the banked partition bricks (pure Finset algebra).  Opus-authored.
-/

theorem solution
    {κ : ℕ → ℕ → ℝ} {S : Finset ℕ} {lam : ℕ → ℝ} {n n' : ℕ} {δ : ℝ}
    (hn : ∀ z ∈ S, lam z ≤ κ n z) (hn' : ∀ z ∈ S, lam z ≤ κ n' z)
    (hmass : δ ≤ ∑ z ∈ S, lam z) :
    δ ≤ ∑ z ∈ S, min (κ n z) (κ n' z) := by
  refine le_trans hmass ?_
  apply Finset.sum_le_sum
  intro z hz
  exact le_min (hn z hz) (hn' z hz)
