-- Prove2me | Theorems.Thm_RecipeBarycenter_ratio_eq_one_iff
-- name    : RecipeBarycenter.ratio_eq_one_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:27:42.336563+00:00
-- url     : https://prove2.me/theorems/9be9b0a2-bad8-4d08-accb-bcb99e473cf2
-- title:
--   Ratio eq one iff
-- statement:
--   Formal statement of `RecipeBarycenter.ratio_eq_one_iff` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RecipeBarycenter.ratio_eq_one_iff{R : Recipe} (hpos : 0 < R.verify) :
--       ratio R = 1 ↔ R.cook = R.verify := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/RecipeBarycenterBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/RecipeBarycenterBridge.lean#L116

-- Thm stub generated from Novelty/RecipeBarycenterBridge.lean
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

theorem RecipeBarycenter.ratio_eq_one_iff{R : Recipe} (hpos : 0 < R.verify) :
    ratio R = 1 ↔ R.cook = R.verify := by sorry
