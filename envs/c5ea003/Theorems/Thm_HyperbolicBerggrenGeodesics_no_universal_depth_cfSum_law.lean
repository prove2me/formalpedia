-- Prove2me | Theorems.Thm_HyperbolicBerggrenGeodesics_no_universal_depth_cfSum_law
-- name    : HyperbolicBerggrenGeodesics.no_universal_depth_cfSum_law
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:28:07.06562+00:00
-- url     : https://prove2.me/theorems/da660e66-efe5-4696-8d23-4f158932ec9b
-- title:
--   Refutation of the continued-fraction law for the depth (conjecture G1).
-- statement:
--   **Refutation of the continued-fraction law for the depth (conjecture G1).**
--   There is *no* constant `λ ≥ 0` for which the depth of a Berggren node equals `λ` times the
--   sum of the partial quotients of its slope up to a bounded error.  The obstruction is
--   explicit: along the right spine the ratio is `1/2`, along the left spine it is `1`, and the
--   linear combination `(depth − λ·cfSum)` of the two families forces `k ≤ 3C + 2λ` for every
--   `k`.
--
--   ```lean
--   theorem HyperbolicBerggrenGeodesics.no_universal_depth_cfSum_law(lam C : ℝ) (hlam : 0 ≤ lam) :
--       ¬ ∀ (m n k : ℕ), Reaches (m, n) k → |(k : ℝ) - lam * (cfSum n m : ℝ)| ≤ C := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/HyperbolicBerggrenTreeDepth.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/HyperbolicBerggrenTreeDepth.lean#L515

-- Thm stub generated from Geometry/HyperbolicBerggrenTreeDepth.lean
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

theorem HyperbolicBerggrenGeodesics.no_universal_depth_cfSum_law(lam C : ℝ) (hlam : 0 ≤ lam) :
    ¬ ∀ (m n k : ℕ), Reaches (m, n) k → |(k : ℝ) - lam * (cfSum n m : ℝ)| ≤ C := by sorry
