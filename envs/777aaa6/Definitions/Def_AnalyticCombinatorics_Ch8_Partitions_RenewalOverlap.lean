-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RenewalOverlap
-- name    : AnalyticCombinatorics_Ch8_Partitions_RenewalOverlap
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:07:05.000267+00:00
-- url     : https://prove2.me/theorems/3d094846-3fe3-4141-ac06-42402ce77be9
-- title:
--   Renewal Overlap
-- statement:
--   The source-linked mathematical setting supplies the finite-kernel, rank, moment, renewal or sequence models used by the exact support contracts in this group. The literal model declarations, where catalogued below, retain their source parameters and assumptions. Definition prose must be refined against the actual complete compiler-derived owner before an upload payload is prepared.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/RenewalOverlap.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# TASK T2.2: the offset law, its exponential escape tail, and the coupling overlap

The engine consumes two facts about the first-crossing **offset law** of the renewal process into a
ceiling, from two delays:

* **escape tail**: the offset exceeds `A` with probability `≤ T A`, where `T A → 0`;
* **overlap**: the two offset laws share a uniformly-positive common part on a fixed top slice.

This file:

1. defines the offset law `offsetLaw p n r r'` = `resKer p n r r'` viewed as the law of the residual
   after `n` unit-level steps from delay `r` (the residual *is* the first-crossing offset when the
   ceiling is `n` levels above the start `r`);
2. proves the **escape tail** `∑'_{r' > A} resKer p n 0 r' ≤ p((A,∞))` from any *renewal* start
   (residual `0`) — rigorously, from the increment exponential tail (the offset can exceed `A` only
   if the crossing increment exceeds `A`);
3. proves the **descent-step overlap minorization**: from delays one renewal apart, the laws
   share mass `≥ p 1` on the slice `{0}` (the increment-`1` minorization), giving `δ`;
4. states the **homogeneous renewal overlap/escape** consequence the engine needs, reducing the
   *uniform-in-delay* overlap to the renewal coalescence fact (the irreducible analytic input).

Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Renewal

/-! ## The increment tail and its exponential bound. -/

/-- Increment tail beyond `A`: the full mass minus the head `∑_{d ≤ A} p d`.  Equivalently
`∑'_{d > A} p d` (see `incrTail_eq_tsum`), but the `1 − partial-sum` form is the convenient one. -/
noncomputable def incrTail (p : ℕ → ℝ) (A : ℕ) : ℝ := 1 - ∑ d ∈ Finset.range (A + 1), p d

/-! ## The stationary offset law (size-biased / residual law).

The residual chain's stationary distribution is `π r' = incrTail p r' / μ`, where
`μ = ∑'_{r'} incrTail p r' = ∑' d, d · p d = E[increment]` is the mean increment.  We build `π`,
prove it is a probability mass (`∑' π = 1`), that it has uniformly-positive mass at the slice `{0}`
(`π 0 = 1/μ > 0`), and that its tail beyond `A` vanishes.  These are precisely the
slice-overlap-floor and escape-vanishing facts the engine needs from the *limiting* offset law.  -/

/-- The increment mean `μ = ∑'_{r'} incrTail p r' = ∑'_d d·p d` (finite, by the exponential tail).
We package it as the tail-sum, which is the form used by the stationary law. -/
noncomputable def incrMean (p : ℕ → ℝ) : ℝ := ∑' r' : ℕ, incrTail p r'

/-- The stationary residual (offset) law: `statOffset p r' = incrTail p r' / incrMean p`. -/
noncomputable def statOffset (p : ℕ → ℝ) (r' : ℕ) : ℝ := incrTail p r' / incrMean p

/-! ## The first-crossing offset law from a delay, and its delay-independence.

The renewal process started at residual (= delay) `s` to the ceiling descends deterministically to a
renewal epoch (residual `0`) in exactly `s` unit-level steps, then draws one increment.  The offset
of the first crossing *after that renewal* is therefore distributed as `p(·+1)` — the increment law
shifted by one — **independently of the delay `s`** (`resKer_descent_then_step`).  This delay-
independence is the engine's coupling: two crossings from two different delays, each measured at its
own first post-descent renewal, share the *identical* offset law, so their common mass on a fixed top
slice is a fixed positive number and is not diluted by widening the band. -/

/-! ## Escape tail of the offset law. -/

/-! ## Common overlap mass of two offset laws on a fixed top slice. -/

/-! ## T2.2 — the homogeneous renewal uniform overshoot/overlap theorem.

Packages the three facts the engine consumes, for an aperiodic exponential-tail integer renewal law:

* a fixed top-slice width `B := 1` and overlap floor `δ := p 1 > 0`, uniform over both delays and over
  the band width `A`;
* a vanishing escape majorant `T A := incrTail p A → 0`;
* for every band width `A ≥ B` and any two delays `s, s'`: the common mass of the two first-crossing
  offset laws on the slice `{0,…,B−1}` is `≥ δ`, and each offset law's escape beyond `A` is `≤ T A`.

The hypotheses `hp_tail`, `hp_aper.2` (i.e. `p 2 > 0`) are recorded for the downstream T2.1/T2.3
interface (the exponential tail certifies the explicit rate; `p 2 > 0` certifies true aperiodicity of
the support, gcd = 1) but the engine-facing overlap/escape pair already follows from `p 1 > 0` and
summability via the delay-independence of the post-renewal offset law. -/

/-! ## Engine-facing bridge: overlap from a uniform single-state minorization.

The variable rank-band engine consumes the overlap as
`δ ≤ ∑_{z ∈ slice} min (κ n z) (κ n' z)` where `κ = enterBandKer Pker (ceilBand …)` and `slice` is
the in-band top slice.  The genuine analytic input is a uniform
*single-state minorization* `κ n z ≥ η` for the two starts on a fixed nonempty subset `S` of the
slice (a Doeblin minorization at the common ceiling).  Once that minorization exists, the overlap is
purely combinatorial: `min (κ n z) (κ n' z) ≥ η` on `S`, so the overlap is `≥ η · |S|`.

This lemma isolates that combinatorial step so the (remaining) analytic minorization plugs straight
into the engine.  It depends on NEITHER the false rank-drop local limit NOR any renewal limit. -/


end AnalyticCombinatorics.Ch8.Partitions.Renewal


