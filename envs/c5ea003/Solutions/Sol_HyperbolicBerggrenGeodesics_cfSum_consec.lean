-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.cfSum_consec
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:45:34.66723+00:00
-- url     : https://prove2.me/submissions/dab52a3d-bc7b-4f35-9c38-c5a31aad22b2

-- Sol generated from Geometry/HyperbolicBerggrenTreeDepth.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenTreeDepth

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


theorem cfSum_zero (n : ℕ) : cfSum n 0 = 0 := by rw [cfSum]

theorem cfSum_succ (n m : ℕ) :
    cfSum n (m + 1) = n / (m + 1) + cfSum (m + 1) (n % (m + 1)) := by rw [cfSum]

theorem cfSum_one_left (M : ℕ) : cfSum M 1 = M := by
  rw [cfSum_succ M 0, Nat.mod_one, cfSum_zero]
  simp






/-! ## Part G. Non-vacuity witnesses -/





open HyperbolicBerggrenGeodesics in
theorem solution(k : ℕ) : cfSum (k + 1) (k + 2) = k + 2 := by
  rw [show k + 2 = (k + 1) + 1 from rfl, cfSum_succ, Nat.div_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num [cfSum_one_left]
  · have hd : (k + 2) / (k + 1) = 1 := by
      refine Nat.div_eq_of_lt_le ?_ ?_ <;> omega
    have hm : (k + 2) % (k + 1) = 1 := by
      rw [Nat.mod_eq_sub_mod (by omega), show k + 2 - (k + 1) = 1 from by omega,
        Nat.mod_eq_of_lt (by omega)]
    rw [cfSum_succ (k + 2) k, hd, hm, cfSum_one_left]
    omega
