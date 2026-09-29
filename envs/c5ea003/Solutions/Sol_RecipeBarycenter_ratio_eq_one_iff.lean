-- Prove2me | solution 1 for RecipeBarycenter.ratio_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:43:04.801338+00:00
-- url     : https://prove2.me/submissions/e928a0d6-7c69-4543-b0a2-4dd034027cd2

-- Sol generated from Novelty/RecipeBarycenterBridge.lean
import Mathlib
import Definitions.Def_Novelty_RecipeBarycenterBridge

/-!
# Recipe complexity as convex geometry

A finite menu is modeled by cooking and verification times.  If every dish has
positive verification time, the cooking/verification ratio of the entire menu is
not an arbitrary quotient: it is the barycenter of the individual ratios, weighted
by each dish's share of the total verification work.

This connects the culinary complexity metaphor to convex geometry.  The bridge has
real content: the weights are nonnegative and sum to one, so an aggregate menu
cannot have a ratio outside the range of its dishes.  Moreover, if every dish is
at least break-even (`V ≤ C`), equality at the boundary is rigid: an aggregate
ratio of one forces every individual ratio to be one.

No claim about actual complexity classes, Navier--Stokes, or soufflé hardness is
made: those would require a computational model and reductions not supplied by
timing data alone.
-/

open RecipeBarycenter





/-
Positive individual verification times imply positive total verification time
when the menu is nonempty.
-/

/-
Verification shares are nonnegative.
-/

/-
The verification shares form a partition of unity.
-/

/-
**Recipe--barycenter bridge.**  The aggregate ratio is the convex combination
of individual ratios weighted by verification work.
-/

/-
The barycenter cannot exceed a common upper bound for all dish ratios.
-/

/-
The barycenter cannot fall below a common lower bound for all dish ratios.
-/

/-
Hence the aggregate ratio lies in every interval containing all individual
ratios: a direct convex-hull statement in one dimension.
-/

/-
A positive-time recipe has ratio one exactly when cooking and verification
costs agree.
-/

/-
**Boundary rigidity.**  If every dish is physical (`V ≤ C`) and every
verification time is positive, then a globally break-even menu is possible exactly
when every dish is individually break-even.  Convex-geometrically, a barycenter of
points in `[1,∞)` equals the boundary point `1` iff every positively weighted point
is `1`.
-/

/-- A concrete three-dish example illustrating the barycentric identity. -/
example :
    ratio (aggregate ![Recipe.mk 6 2, Recipe.mk 12 3, Recipe.mk 5 5]) =
      (2 / 10 : ℚ) * 3 + (3 / 10 : ℚ) * 4 + (5 / 10 : ℚ) * 1 := by
  norm_num [ratio, aggregate, Fin.sum_univ_succ]


open RecipeBarycenter in
theorem solution{R : Recipe} (hpos : 0 < R.verify) :
    ratio R = 1 ↔ R.cook = R.verify := by
  unfold ratio; rw [ div_eq_iff ] <;> norm_cast ; aesop;
  linarith
