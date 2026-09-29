-- Prove2me | Definitions.Def_Geometry_HyperbolicBerggrenTreeDepth
-- name    : Geometry_HyperbolicBerggrenTreeDepth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:26:15.030089+00:00
-- url     : https://prove2.me/theorems/d4e46c65-cc78-4d03-8f25-b3145e506bc3
-- title:
--   Aether Catalog definitions — Geometry_HyperbolicBerggrenTreeDepth
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.HyperbolicBerggrenTreeDepth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/HyperbolicBerggrenTreeDepth.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics

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

namespace HyperbolicBerggrenGeodesics

open Real

/-! ## Part A. Reachability in the Berggren tree -/

/-- `Reaches p k` : the pair `p` is produced from the root Euclid seed `(2,1)` by exactly `k`
Berggren moves. -/
inductive Reaches : ℕ × ℕ → ℕ → Prop
  | root : Reaches (2, 1) 0
  | stepL {p k} : Reaches p k → Reaches (seedL p) (k + 1)
  | stepM {p k} : Reaches p k → Reaches (seedM p) (k + 1)
  | stepR {p k} : Reaches p k → Reaches (seedR p) (k + 1)


/-- The hypotenuse of the Pythagorean triple attached to a pair. -/
def hypot (p : ℕ × ℕ) : ℕ := p.1 ^ 2 + p.2 ^ 2

/-! ## Part B. The inverse move, and completeness of the tree -/

/-- The **parent** of a Euclid seed `(M,N)`, i.e. the inverse Berggren move.  Which of the
three moves produced `(M,N)` is decided by the position of `M` relative to `2N` and `3N`
— equivalently by the position of the slope `N/M` relative to `1/2` and `1/3`. -/
def parentSeed (p : ℕ × ℕ) : ℕ × ℕ :=
  if 2 * p.2 < p.1 then
    (if 3 * p.2 < p.1 then (p.1 - 2 * p.2, p.2) else (p.2, p.1 - 2 * p.2))
  else (p.2, 2 * p.2 - p.1)










/-! ## Part C. Uniqueness of the depth -/




/-! ## Part D. Depth versus size: the lower bound -/






/-! ## Part E. Depth versus size: the matching upper bound along the Pell spine -/

/-- The **middle spine**: iterate the Berggren move `B₂` from the root.  Its first
coordinates `2, 5, 12, 29, 70, …` are the Pell numbers. -/
def mspine : ℕ → ℕ × ℕ
  | 0 => (2, 1)
  | k + 1 => seedM (mspine k)







/-! ## Part F. Depth is not governed by the continued fraction of the slope

The natural guess (conjecture **G1** of `FUTURE_DIRECTIONS.md`) is that a Berggren path is
the additive continued-fraction expansion of the slope `n/m`, so that the depth should equal
the sum of the partial quotients up to a bounded error, or at least up to a fixed
proportionality constant.  This is **false**, and the reason is structural: the move `B₃`
adds `2` to `m/n`, so a long run of `B₃`'s costs only *half* a partial quotient per step,
while the move `B₁` accumulates at the parabolic fixed point `n/m = 1` and costs a *whole*
partial quotient per step.  The two pure spines therefore realise two different
proportionality constants, and no single law can hold. -/

/-- The sum of the partial quotients of the continued fraction of `n/m`
(`cfSum n m = a₁ + a₂ + ⋯` when `n < m`). -/
def cfSum : ℕ → ℕ → ℕ
  | _, 0 => 0
  | n, (m + 1) => n / (m + 1) + cfSum (m + 1) (n % (m + 1))
  termination_by _ m => m
  decreasing_by exact Nat.mod_lt _ (Nat.succ_pos m)









/-! ## Part G. Non-vacuity witnesses -/




end HyperbolicBerggrenGeodesics


