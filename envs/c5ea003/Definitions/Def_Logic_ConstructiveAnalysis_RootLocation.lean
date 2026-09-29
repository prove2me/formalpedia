-- Prove2me | Definitions.Def_Logic_ConstructiveAnalysis_RootLocation
-- name    : Logic_ConstructiveAnalysis_RootLocation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:52:48.226977+00:00
-- url     : https://prove2.me/theorems/e7a37011-7f61-4290-b8b2-0a1badfdc5de
-- title:
--   Aether Catalog definitions — Logic_ConstructiveAnalysis_RootLocation
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.ConstructiveAnalysis.RootLocation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/ConstructiveAnalysis/RootLocation.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveIVT
/-
# Locating roots: what the grid search really delivers

`Bishop.exists_grid_abs_le` produces a grid point at which `|f|` is small.  Turning a
*small value* into a *small distance to a root* is the delicate step of the
intermediate value theorem, and `Bishop.constructive_ivt` does it with a global slope
bound `c > 0`, at the price of the factor `1/c`.

This file isolates the two sides of that step.

* `Bishop.exists_grid_near_root` : **the bracketing form of the search**.  With no
  non-degeneracy hypothesis whatsoever — only a modulus of uniform continuity and the
  sign condition `f a ≤ 0 ≤ f b` — the *sign-change* grid search returns a grid point
  within one mesh `(b-a)/N` of a genuine root.  The location comes from the bracket
  `f (grid k) ≤ 0 < f (grid (k+1))`, not from the size of `|f|`.

* `Bishop.local_nonconstancy_insufficient` : **a bound on `|f|` alone is not enough**,
  even under Bishop's local non-constancy hypothesis with an explicit modulus `ν`.
  The `1`-Lipschitz function `Bishop.dipFn η x = min (x-1) (|x-3| + η)` has the unique
  root `1`, satisfies local non-constancy with the explicit modulus `ν h = h/8`, and
  yet `|dipFn η 3| = η` is as small as one likes while `3` is at distance `2` from the
  root.  So no theorem of the form "`|f x|` small ⟹ `x` near a root" can be derived
  from local non-constancy alone.
-/


namespace Bishop

open Set

/-! ## 1. The bracketing form of the grid search -/


/-! ## 2. Local non-constancy does not locate approximate roots

Bishop's exact intermediate value theorem replaces a slope bound by *local
non-constancy*.  The following explicit function shows that this hypothesis, even
with an explicit modulus `ν`, does not let one conclude that a point with small
`|f|` is close to a root. -/

/-- A `1`-Lipschitz function on `[0,4]` with the single root `1` and a "near root" of
depth `η` at `x = 3`. -/
noncomputable def dipFn (η x : ℝ) : ℝ := min (x - 1) (|x - 3| + η)









end Bishop


