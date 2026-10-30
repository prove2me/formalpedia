-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_overlap_ge_of_common_submeasure
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.overlap_ge_of_common_submeasure
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:38:37.612983+00:00
-- url     : https://prove2.me/theorems/5ca1eb0e-362a-4c8e-8201-e05b98dbcd96
-- title:
--   A finite overlap lower bound from a common dominated function
-- statement:
--   Let $S\subset\mathbb N$ be finite, $\kappa:\mathbb N^2\to\mathbb R$, $\lambda:\mathbb N\to\mathbb R$ and $\delta\in\mathbb R$. If $\lambda(z)\le\kappa(n,z)$ and $\lambda(z)\le\kappa(n^{\prime},z)$ for all $z\in S$, and $\delta\le\sum_{z\in S}\lambda(z)$, then $$\delta\le\sum_{z\in S}\min(\kappa(n,z),\kappa(n^{\prime},z)).$$ There is no nonnegativity premise on $\lambda$ or either row.
--
--   This support estimate carries the following complete literal source contract:
--
--   ```lean
--   lemma overlap_ge_of_common_submeasure
--       {κ : ℕ → ℕ → ℝ} {S : Finset ℕ} {lam : ℕ → ℝ} {n n' : ℕ} {δ : ℝ}
--       (hn : ∀ z ∈ S, lam z ≤ κ n z) (hn' : ∀ z ∈ S, lam z ≤ κ n' z)
--       (hmass : δ ≤ ∑ z ∈ S, lam z) :
--       δ ≤ ∑ z ∈ S, min (κ n z) (κ n' z)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/CommonSubmeasure.lean#L32. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.overlap_ge_of_common_submeasure
    {κ : ℕ → ℕ → ℝ} {S : Finset ℕ} {lam : ℕ → ℝ} {n n' : ℕ} {δ : ℝ}
    (hn : ∀ z ∈ S, lam z ≤ κ n z) (hn' : ∀ z ∈ S, lam z ≤ κ n' z)
    (hmass : δ ≤ ∑ z ∈ S, lam z) :
    δ ≤ ∑ z ∈ S, min (κ n z) (κ n' z) := by sorry
