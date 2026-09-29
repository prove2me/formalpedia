-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.mspine_dist_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:25:05.899244+00:00
-- url     : https://prove2.me/submissions/46fffe14-18cd-4316-a037-960416a49b1c

-- Sol generated from Geometry/HyperbolicBerggrenTreeDepth.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Definitions.Def_Geometry_HyperbolicBerggrenTreeDepth
import Theorems.Thm_HyperbolicBerggrenGeodesics_hyperbolic_dist_eq_half_log_hypotenuse
import Theorems.Thm_HyperbolicBerggrenGeodesics_mspine_isSeed

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




/-- The middle spine grows at least geometrically: `m_k ≥ 2^{k+1}`. -/
theorem mspine_fst_ge (k : ℕ) : 2 ^ (k + 1) ≤ (mspine k).1 := by
  induction k with
  | zero => simp [mspine]
  | succ k ih =>
      have hs := mspine_isSeed k
      have h1 : (mspine (k + 1)).1 = 2 * (mspine k).1 + (mspine k).2 := rfl
      rw [h1, pow_succ]
      have := hs.pos
      omega

/-- Consequently the hypotenuse along the middle spine is at least `4^{k+1}`. -/
theorem mspine_hypot_ge (k : ℕ) : 4 ^ (k + 1) ≤ hypot (mspine k) := by
  have h := mspine_fst_ge k
  have h4 : (4 : ℕ) ^ (k + 1) = (2 ^ (k + 1)) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  calc (4 : ℕ) ^ (k + 1) = (2 ^ (k + 1)) ^ 2 := h4
    _ ≤ (mspine k).1 ^ 2 := Nat.pow_le_pow_left h 2
    _ ≤ hypot (mspine k) := by simp [hypot]



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
theorem solution(k : ℕ) :
    (k : ℝ) * Real.log 2 ≤
      dist (hpoint (mspine k).1 (mspine k).2
        (lt_trans (mspine_isSeed k).pos (mspine_isSeed k).lt)) UpperHalfPlane.I := by
  have hs := mspine_isSeed k
  have habs := hyperbolic_dist_eq_half_log_hypotenuse (m := (mspine k).1) (n := (mspine k).2)
    hs.pos hs.lt
  have h1 := (abs_le.mp habs).1
  have hnat := mspine_hypot_ge k
  have hc : (4 : ℝ) ^ (k + 1) ≤ ((mspine k).1 : ℝ) ^ 2 + ((mspine k).2 : ℝ) ^ 2 := by
    have : ((4 ^ (k + 1) : ℕ) : ℝ) ≤ ((hypot (mspine k) : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa [hypot] using this
  have hlog : Real.log ((4 : ℝ) ^ (k + 1)) ≤
      Real.log (((mspine k).1 : ℝ) ^ 2 + ((mspine k).2 : ℝ) ^ 2) :=
    Real.log_le_log (by positivity) hc
  have h4 : Real.log ((4 : ℝ) ^ (k + 1)) = ((k : ℝ) + 1) * (2 * Real.log 2) := by
    rw [Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h4] at hlog
  linarith
