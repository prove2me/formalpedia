-- Prove2me | solution 1 for CakeBalancing.mu_smul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:15:06.313305+00:00
-- url     : https://prove2.me/submissions/0a0a1570-1482-4d8a-b2af-4c51242ad2ec

-- Sol generated from Applications/CakeBalancing/Basic.lean
import Mathlib
import Definitions.Def_Applications_CakeBalancing_Basic

/-!
# The cake-balancing ratio functional

Consider a circular cake whose boundary carries finitely many cut points.  When
`n` cuts are present they divide the circle into `n` arcs (the *pieces*).  Fix a
window length `r ≥ 1`.  For each starting position `i` the sum of the `r`
consecutive pieces `i, i+1, …, i+r-1` (indices read cyclically) is a *window
weight*.  The **balancing ratio**

`μ_r = (largest window weight) / (smallest window weight)`

measures how far the current dissection is from perfectly balancing every block
of `r` consecutive pieces.  A dissection is perfectly balanced for windows of
length `r` exactly when `μ_r = 1`.

This file develops the exact, dimension-free algebra of this functional for a
single dissection.  A circular dissection into `n` pieces is modelled by a
positive weight function `arc : ZMod n → ℝ`, the cyclic group `ZMod n`
supplying the wrap-around index arithmetic for free.

The headline structural results are:

* `mu_ge_one` — the ratio is always at least `1`;
* `mu_le_arcRatio` / `mu_le_mu_one` — **aggregation never increases imbalance**:
  the window ratio for any `r ≥ 1` is bounded by the ratio of the single largest
  to the single smallest piece;
* `mu_smul` — the ratio is scale invariant, so the circumference is irrelevant;
* `mu_equipartition` — an equipartition realises the optimal value `1`.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  Grouping consecutive pieces should *average out*
local fluctuations, so the imbalance seen through a window of length `r` can
never exceed the raw piece-to-piece imbalance `μ_1 = maxArc / minArc`.  We
conjectured the sharp comparison `μ_r ≤ μ_1` for every `r ≥ 1`, together with
scale invariance and attainment of `1` at the equipartition.

EXPERIMENT (Experimenter).  Each window weight is a sum of `r` pieces, hence
sandwiched between `r · minArc` and `r · maxArc`.  Passing to the extremal
windows and cancelling the common factor `r` yields `μ_r ≤ maxArc / minArc`, and
`μ_1 = maxArc / minArc` because a length-one window is a single piece.

ANALYSIS (Analyst).  The factor `r` cancels *exactly*; the comparison is not an
asymptotic estimate but an identity-driven inequality valid for every finite
dissection.  Positivity of the pieces is the only hypothesis that does real
work (it keeps the denominator away from `0`).

CRITIQUE (Critic).  The results are non-vacuous: the equipartition witnesses
equality in `mu_ge_one`, and two-valued dissections (see the companion file)
witness strict inequality, so neither bound is degenerate.  The boundary case
`r = 0` (empty window) is excluded exactly as the informal statement demands
`r ≥ 1`.
-/

open Finset

open CakeBalancing

variable {n : ℕ}




















/-! ### Examples -/

-- The functionals are well defined for every window length.
#check @mu


open CakeBalancing in
theorem solution[NeZero n] (arc : ZMod n → ℝ) {c : ℝ} (hc : 0 < c) (r : ℕ) :
    mu (fun i => c * arc i) r = mu arc r := by
  unfold mu;
  unfold maxWindow minWindow;
  unfold windowSum;
  simp only [← Finset.mul_sum] ;
  rw [ show ( Finset.univ.sup' _ fun x => c * ∑ i ∈ Finset.range r, arc ( x + i ) ) = c * ( Finset.univ.sup' _ fun x => ∑ i ∈ Finset.range r, arc ( x + i ) ) from ?_, show ( Finset.univ.inf' _ fun x => c * ∑ i ∈ Finset.range r, arc ( x + i ) ) = c * ( Finset.univ.inf' _ fun x => ∑ i ∈ Finset.range r, arc ( x + i ) ) from ?_ ];
  any_goals exact Finset.univ_nonempty;
  · rw [ mul_div_mul_left _ _ hc.ne' ];
  · refine' le_antisymm _ _ <;> simp +decide;
    · have := Finset.exists_min_image Finset.univ ( fun x => ∑ i ∈ Finset.range r, arc ( x + i ) ) ⟨ 0, Finset.mem_univ 0 ⟩ ; aesop;
    · exact fun x => mul_le_mul_of_nonneg_left ( Finset.inf'_le _ <| Finset.mem_univ _ ) hc.le;
  · refine' le_antisymm _ _ <;> simp +decide [ Finset.sup'_le_iff, Finset.le_sup'_iff ];
    · exact fun x => mul_le_mul_of_nonneg_left ( Finset.le_sup' ( fun x => ∑ i ∈ Finset.range r, arc ( x + i ) ) ( Finset.mem_univ x ) ) hc.le;
    · have := Finset.exists_max_image Finset.univ ( fun x => ∑ i ∈ Finset.range r, arc ( x + i ) ) ⟨ 0, Finset.mem_univ 0 ⟩ ; aesop;
