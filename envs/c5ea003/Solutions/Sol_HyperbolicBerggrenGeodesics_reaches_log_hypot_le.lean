-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.reaches_log_hypot_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:58:15.044148+00:00
-- url     : https://prove2.me/submissions/ace19054-6a31-44fa-bc8b-0aab21e7f35c

-- Sol generated from Geometry/HyperbolicBerggrenTreeDepth.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Definitions.Def_Geometry_HyperbolicBerggrenTreeDepth
import Theorems.Thm_HyperbolicBerggrenGeodesics_reaches_hypot_le
import Theorems.Thm_HyperbolicBerggrenGeodesics_reaches_isSeed

/-!
# Hyperbolic–Pythagorean Geodesics, cycle VIII: the tree structure of the depth function

Cycles I–VII studied a *single* Berggren node `(m,n)` and the effect of one Berggren move
on its hyperbolic position.  The quantity that the mission statement is really about — the
**path length**, i.e. the combinatorial depth `k` at which a node occurs — was so far only
touched in the negative (`depth_not_bounded_by_distance`: depth is not bounded by a constant
multiple of the hyperbolic distance).  This file settles the positive half and the
book-keeping that makes "the depth" a well-defined function in the first place.

## Main results

* `Reaches p k` : the inductive predicate "`p` is obtained from the root seed `(2,1)` by `k`
  Berggren moves".
* `reaches_isSeed` : every reachable pair is a Euclid seed (soundness).
* `seed_reaches` : **completeness of the Berggren tree.** *Every* Euclid seed is reachable.
  The proof runs the explicit inverse move `parentSeed`, which is a genuine trichotomy in
  the slope: `n/m ∈ (1/2, 1)`, `(1/3, 1/2)`, `(0, 1/3)` selects `B₁`, `B₂`, `B₃`.
* `reaches_unique` : **the Berggren tree really is a tree.**  A seed is reachable at exactly
  one depth, so `depth` is a well-defined function on seeds.
* `reaches_fst_le` : a node at depth `k` has `m ≤ 2·3^k`; hence
  `reaches_log_hyp_le` : `log c ≤ log 8 + k · log 9`, and
  `dist_le_depth` / `depth_ge_dist` : `2 d(i, z) ≤ log 32 + k · log 9`, i.e.
  **the hyperbolic distance is, up to constants, a lower bound for the depth**.
  Combined with `depth_not_bounded_by_distance` of cycle I this is the exact truth:
  `d ≲ k`, and no reverse inequality holds.
* `mspine_dist_ge` : along the middle (Pell) spine the reverse inequality *does* hold,
  `k · log 2 ≤ d`, so on that branch depth and distance are commensurable.
* `berggren_depth_logarithmic_reach` : **the `O(log N)` statement of the mission, in the
  only form in which it is true.**  For every `N` there is a Berggren node of hypotenuse
  `≥ N` at depth `k = ⌊log₂ N⌋`, and `k · log 2 ≤ log N`.

Together: reaching size `N` costs depth `Θ(log N)` at best (`berggren_depth_logarithmic_reach`
for the upper bound, `depth_ge_dist` for the matching lower bound), while an arbitrary node of
hypotenuse `N` can sit at depth as large as `Θ(√N)` (cycle I).
-/

open HyperbolicBerggrenGeodesics

open Real

/-! ## Part A. Reachability in the Berggren tree -/




/-! ## Part B. The inverse move, and completeness of the tree -/











/-! ## Part C. Uniqueness of the depth -/




/-! ## Part D. Depth versus size: the lower bound -/






/-! ## Part E. Depth versus size: the matching upper bound along the Pell spine -/








/-! ## Part F. Depth is not governed by the continued fraction of the slope

The natural guess (conjecture **G1** of `FUTURE_DIRECTIONS.md`) is that a Berggren path is
the additive continued-fraction expansion of the slope `n/m`, so that the depth should equal
the sum of the partial quotients up to a bounded error, or at least up to a fixed
proportionality constant.  This is **false**, and the reason is structural: the move `B₃`
adds `2` to `m/n`, so a long run of `B₃`'s costs only *half* a partial quotient per step,
while the move `B₁` accumulates at the parabolic fixed point `n/m = 1` and costs a *whole*
partial quotient per step.  The two pure spines therefore realise two different
proportionality constants, and no single law can hold. -/










/-! ## Part G. Non-vacuity witnesses -/





open HyperbolicBerggrenGeodesics in
theorem solution{p : ℕ × ℕ} {k : ℕ} (h : Reaches p k) :
    Real.log ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ≤ Real.log 8 + k * Real.log 9 := by
  have hnat := reaches_hypot_le h
  have hs := reaches_isSeed h
  have hpos : 0 < p.1 := lt_trans hs.pos hs.lt
  have hc : ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ≤ 8 * 9 ^ k := by
    have : ((hypot p : ℕ) : ℝ) ≤ ((8 * 9 ^ k : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa [hypot] using this
  have hcpos : (0 : ℝ) < (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
    have : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hpos
    positivity
  calc Real.log ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)
      ≤ Real.log (8 * 9 ^ k) := Real.log_le_log hcpos hc
    _ = Real.log 8 + k * Real.log 9 := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
