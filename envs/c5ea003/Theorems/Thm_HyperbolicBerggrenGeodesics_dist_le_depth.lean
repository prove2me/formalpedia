-- Prove2me | Theorems.Thm_HyperbolicBerggrenGeodesics_dist_le_depth
-- name    : HyperbolicBerggrenGeodesics.dist_le_depth
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T20:15:32.739679+00:00
-- url     : https://prove2.me/theorems/4c5aee84-9ac2-4edb-a07e-cefe39583fdd
-- title:
--   The hyperbolic distance is a lower bound for the depth.
-- statement:
--   **The hyperbolic distance is a lower bound for the depth.**  If a node sits at depth `k`
--   in the Berggren tree then `2 · d(i, z) ≤ log 32 + k · log 9`.  Together with
--   `depth_not_bounded_by_distance` (cycle I), which shows no reverse inequality can hold, this
--   pins down exactly the relation between the metric and the combinatorics.
--
--   ```lean
--   theorem HyperbolicBerggrenGeodesics.dist_le_depth{p : ℕ × ℕ} {k : ℕ} (h : Reaches p k) :
--       2 * dist (hpoint p.1 p.2 (lt_trans (reaches_isSeed h).pos (reaches_isSeed h).lt))
--         UpperHalfPlane.I ≤ Real.log 32 + k * Real.log 9 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/HyperbolicBerggrenTreeDepth.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/HyperbolicBerggrenTreeDepth.lean#L333

-- Thm stub generated from Geometry/HyperbolicBerggrenTreeDepth.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Definitions.Def_Geometry_HyperbolicBerggrenTreeDepth
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

theorem HyperbolicBerggrenGeodesics.dist_le_depth{p : ℕ × ℕ} {k : ℕ} (h : Reaches p k) :
    2 * dist (hpoint p.1 p.2 (lt_trans (reaches_isSeed h).pos (reaches_isSeed h).lt))
      UpperHalfPlane.I ≤ Real.log 32 + k * Real.log 9 := by sorry
