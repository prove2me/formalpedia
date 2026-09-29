-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.seed_reaches
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:09:08.928593+00:00
-- url     : https://prove2.me/submissions/371790a4-fb7f-4621-a4d6-0074551b9429

-- Sol generated from Geometry/HyperbolicBerggrenTreeDepth.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Definitions.Def_Geometry_HyperbolicBerggrenTreeDepth
import Theorems.Thm_HyperbolicBerggrenGeodesics_parentSeed_isSeed
import Theorems.Thm_HyperbolicBerggrenGeodesics_seed_eq_child_parentSeed

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








/-- The parent of a non-root Euclid seed is strictly smaller in its first coordinate. -/
theorem parentSeed_fst_lt {m n : ℕ} (h : IsSeed m n) : (parentSeed (m, n)).1 < m := by
  have hpos := h.pos
  have hlt := h.lt
  by_cases hA : 2 * n < m
  · by_cases hB : 3 * n < m
    · simp only [parentSeed, if_pos hA, if_pos hB]; omega
    · simp only [parentSeed, if_pos hA, if_neg hB]; omega
  · simp only [parentSeed, if_neg hA]; omega



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
theorem solution: ∀ (m : ℕ), ∀ (n : ℕ), IsSeed m n → ∃ k, Reaches (m, n) k := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n h
    by_cases hroot : m = 2 ∧ n = 1
    · exact ⟨0, by rw [hroot.1, hroot.2]; exact Reaches.root⟩
    · obtain ⟨k, hk⟩ :=
        ih (parentSeed (m, n)).1 (parentSeed_fst_lt h) (parentSeed (m, n)).2
          (parentSeed_isSeed h hroot)
      rcases seed_eq_child_parentSeed h with hc | hc | hc
      · exact ⟨k + 1, by rw [hc]; exact Reaches.stepL hk⟩
      · exact ⟨k + 1, by rw [hc]; exact Reaches.stepM hk⟩
      · exact ⟨k + 1, by rw [hc]; exact Reaches.stepR hk⟩
