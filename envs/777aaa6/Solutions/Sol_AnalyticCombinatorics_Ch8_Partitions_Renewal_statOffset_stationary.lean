-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Renewal.statOffset_stationary
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:10:27.631359+00:00
-- url     : https://prove2.me/submissions/eed2ec75-8ada-46f0-a15e-66b1b752ca1a

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RenewalCore
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RenewalOffset
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RenewalOverlap
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
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

lemma resStep_zero (p : ℕ → ℝ) (r' : ℕ) : resStep p 0 r' = p (r' + 1) := rfl

lemma resStep_succ (p : ℕ → ℝ) (r r' : ℕ) :
    resStep p (r+1) r' = if r' = r then 1 else 0 := rfl

end AnalyticCombinatorics.Ch8.Partitions.Renewal
end
end

section
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

/-- The increment tail equals the complement `tsum` `∑'_{d : ↑(range (A+1))ᶜ} p d`. -/
lemma incrTail_eq_tsum {p : ℕ → ℝ} (hl : IsIncrementLaw p) (A : ℕ) :
    incrTail p A = ∑' d : ((Finset.range (A + 1) : Set ℕ)ᶜ : Set ℕ), p d := by
  classical
  have hsplit := hl.summable.sum_add_tsum_compl (s := Finset.range (A + 1))
  rw [hl.total] at hsplit
  rw [incrTail]
  linarith [hsplit]

/-- The increment tail is nonnegative. -/
lemma incrTail_nonneg {p : ℕ → ℝ} (hl : IsIncrementLaw p) (A : ℕ) : 0 ≤ incrTail p A := by
  rw [incrTail_eq_tsum hl]
  exact tsum_nonneg (fun d => hl.nonneg d.1)

/-! ## The stationary offset law (size-biased / residual law).

The residual chain's stationary distribution is `π r' = incrTail p r' / μ`, where
`μ = ∑'_{r'} incrTail p r' = ∑' d, d · p d = E[increment]` is the mean increment.  We build `π`,
prove it is a probability mass (`∑' π = 1`), that it has uniformly-positive mass at the slice `{0}`
(`π 0 = 1/μ > 0`), and that its tail beyond `A` vanishes.  These are precisely the
slice-overlap-floor and escape-vanishing facts the engine needs from the *limiting* offset law.  -/

/-- The mean is positive once the law has any mass beyond `0` — in particular under aperiodicity
`p 1 > 0` (since `incrTail p 0 = 1 - p 0 = 1 > 0`). -/
lemma incrMean_pos {p : ℕ → ℝ} (hl : IsIncrementLaw p)
    (hsum : Summable (incrTail p)) : 0 < incrMean p := by
  rw [incrMean]
  -- incrTail p 0 = 1 - p 0 = 1 > 0, so the (nonneg) tail-sum is ≥ that single term > 0
  have h0 : incrTail p 0 = 1 := by
    rw [incrTail]; simp [hl.zero]
  have hle : incrTail p 0 ≤ ∑' r', incrTail p r' :=
    Summable.le_tsum hsum 0 (fun r' _ => incrTail_nonneg hl r')
  rw [h0] at hle; linarith

end AnalyticCombinatorics.Ch8.Partitions.Renewal
end
end

/-!
# The reference measure π for the renewal residual chain (sector route)

The sector/Dirichlet route to the renewal Green lower bound needs a reference measure `π` on the
residual chain `resStep p` (RenewalOffset) for which the antisymmetric cut-flux is controlled.  The
crucial structural property is **stationarity**: for a stationary `π`, the cut-flux *divergence*
`divJ(x) = π_x·rowsum − ∑_y π_y K(y,x)` vanishes identically, so the divergence term of the exact cut
identity `aAnti = −½∑ divJ·f·g − ∑ Hcut·grad` drops and the sector reduces to the genuine crossing
variation.

This file constructs that reference measure as the already-built size-biased offset law
`statOffset p = incrTail p / incrMean p` (RenewalOverlap) and proves it is **stationary** for the
residual chain:

  `∑'_r statOffset p r · resStep p r r' = statOffset p r'`.

The residual row `r ↦ resStep p r r'` is supported on exactly `{0, r'+1}` (jump from `0`, or
deterministic descent from `r'+1`), so the `tsum` is a two-term sum; stationarity then follows from
the tail recurrence `incrTail p r' = p(r'+1) + incrTail p (r'+1)` and `statOffset p 0 = 1/μ`.

This is the reference-measure half of `erdos_rankdiff_sector_input`; the remaining sector input is the
quantitative crossing-variation (cut-flux) bound, which the sector route needs *instead* of a
rank-drop local limit (the latter being the documented floor-rank `⌊3√n⌋` obstruction).
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Renewal

/-- **Tail recurrence**: `incrTail p A = p(A+1) + incrTail p (A+1)`. -/
lemma incrTail_succ (p : ℕ → ℝ) (A : ℕ) :
    incrTail p A = p (A + 1) + incrTail p (A + 1) := by
  have hss : (∑ d ∈ Finset.range (A + 1 + 1), p d)
      = (∑ d ∈ Finset.range (A + 1), p d) + p (A + 1) := Finset.sum_range_succ p (A + 1)
  unfold incrTail
  rw [hss]; ring

end AnalyticCombinatorics.Ch8.Partitions.Renewal
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Renewal
open Filter Topology BigOperators
theorem solution {p : ℕ → ℝ} (hl : IsIncrementLaw p)
    (hsum : Summable (incrTail p)) (r' : ℕ) :
    ∑' r, statOffset p r * resStep p r r' = statOffset p r' := by
  classical
  have hμ : 0 < incrMean p := incrMean_pos hl hsum
  -- the residual row in `r` is supported on `{0, r'+1}`
  have hsupp : ∀ r ∉ ({0, r' + 1} : Finset ℕ), statOffset p r * resStep p r r' = 0 := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
    obtain ⟨hr0, hr1⟩ := hr
    obtain _ | m := r
    · exact absurd rfl hr0
    · rw [resStep_succ, if_neg (by omega : ¬ r' = m), mul_zero]
  rw [tsum_eq_sum hsupp, Finset.sum_pair (by omega : (0 : ℕ) ≠ r' + 1)]
  rw [resStep_zero, resStep_succ, if_pos rfl, mul_one]
  -- goal: statOffset p 0 * p (r'+1) + statOffset p (r'+1) = statOffset p r'
  have h0 : incrTail p 0 = 1 := by unfold incrTail; simp [hl.zero]
  have htail := incrTail_succ p r'
  unfold statOffset
  rw [h0, htail]
  field_simp
