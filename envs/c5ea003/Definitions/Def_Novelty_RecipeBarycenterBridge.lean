-- Prove2me | Definitions.Def_Novelty_RecipeBarycenterBridge
-- name    : Novelty_RecipeBarycenterBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:30:08.757281+00:00
-- url     : https://prove2.me/theorems/27444dad-94c7-4400-a696-177b674b2c1c
-- title:
--   Aether Catalog definitions — Novelty_RecipeBarycenterBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.RecipeBarycenterBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/RecipeBarycenterBridge.lean by skeleton subtraction
import Mathlib

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

namespace RecipeBarycenter

/-- A recipe represented by cooking time and verification time. -/
structure Recipe where
  cook : ℕ
  verify : ℕ

/-- Cooking-to-verification ratio. -/
noncomputable def ratio (R : Recipe) : ℚ := (R.cook : ℚ) / (R.verify : ℚ)

/-- Aggregate a finite menu by adding both resource costs. -/
noncomputable def aggregate {ι : Type*} [Fintype ι] (R : ι → Recipe) : Recipe where
  cook := ∑ i, (R i).cook
  verify := ∑ i, (R i).verify

/-- The verification-work share of dish `i`. -/
noncomputable def weight {ι : Type*} [Fintype ι] (R : ι → Recipe) (i : ι) : ℚ :=
  ((R i).verify : ℚ) / ((aggregate R).verify : ℚ)

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

end RecipeBarycenter


